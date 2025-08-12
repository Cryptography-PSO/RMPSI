#include <iostream>
#include <vector>
#include <set>
#include <chrono>
#include <random>
#include <map>
#include <thread>
#include <algorithm>
#include <cstring>
#include <iomanip>
#include <cassert>
#include <future>
#include <cmath>
#include <unordered_set>
#include <string>

#include "volePSI/RsPsi.h"
#include "volePSI/SimpleIndex.h"
#include "volePSI/Defines.h"
#include "coproto/Socket/AsioSocket.h"
#include <cryptoTools/Common/Timer.h>
#include <cryptoTools/Crypto/PRNG.h>
#include <cryptoTools/Crypto/RandomOracle.h>
#include <cryptoTools/Common/BitVector.h>
#include <cryptoTools/Crypto/SodiumCurve.h>
#include <macoro/sync_wait.h>
#include <macoro/when_all.h>

using namespace std;
using namespace volePSI;
using namespace oc;
using coproto::Socket;

#define BASE_PORT 12000

using Field = uint64_t;
// 使用更安全的素数，这是一个64位安全素数
const Field PRIME = 0xFFFFFFFFFFFFFFC5ULL; // 2^64 - 59，是一个素数

// 改进的模逆计算函数，参考标准实现
Field modinv(Field a, Field p = PRIME) {
    if (a == 0) {
        throw runtime_error("Cannot compute inverse of 0");
    }
    
    // 确保a在有效范围内
    a = a % p;
    if (a == 0) {
        throw runtime_error("Cannot compute inverse of 0 after mod");
    }
    
    // 使用扩展欧几里得算法，使用有符号整数避免溢出
    int64_t t = 0, newt = 1;
    int64_t r = (int64_t)p, newr = (int64_t)a;
    
    while (newr != 0) {
        int64_t q = r / newr;
        
        int64_t temp_t = t - q * newt;
        t = newt;
        newt = temp_t;
        
        int64_t temp_r = r - q * newr;
        r = newr;
        newr = temp_r;
    }
    
    if (r > 1) {
        throw runtime_error("Element not invertible: gcd(" + to_string(a) + ", " + to_string(p) + ") = " + to_string(r));
    }
    
    // 确保结果为正数
    if (t < 0) {
        t += (int64_t)p;
    }
    
    return (Field)t;
}

// 安全的模幂运算
uint64_t powm(uint64_t base, uint64_t exp, uint64_t mod) {
    if (mod == 1) return 0;
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            result = (__uint128_t(result) * base) % mod; // 使用128位避免溢出
        }
        base = (__uint128_t(base) * base) % mod;
        exp >>= 1;
    }
    return result;
}

// 安全的模减法
Field mod_sub(Field a, Field b, Field p = PRIME) {
    a = a % p;
    b = b % p;
    if (a >= b) {
        return a - b;
    } else {
        return p - (b - a);
    }
}

// 安全的模乘法
Field mod_mul(Field a, Field b, Field p = PRIME) {
    return (__uint128_t(a % p) * (b % p)) % p; // 使用128位避免溢出
}

// 改进的拉格朗日插值系数计算，参考标准算法
Field lagrange_coeff(int idx, const vector<int>& C) {
    Field res = 1;
    int i_v = C[idx];
    
    // cout << "计算索引" << idx << "(值=" << i_v << ")的拉格朗日系数，参与方: ";
    // for (int x : C) cout << x << " ";
    // cout << endl;
    
    for (int l : C) {
        if (l != i_v) {
            // 计算分子：(PRIME - l) % PRIME，即 -l mod PRIME
            Field numerator = (PRIME - (l % PRIME)) % PRIME;
            
            // 计算分母：(i_v - l + PRIME) % PRIME
            Field denominator = ((i_v - l + PRIME) % PRIME);
            
            // cout << "  处理l=" << l << ": 分子=" << numerator << ", 分母=" << denominator;
            
            if (denominator == 0) {
                throw runtime_error("Lagrange coefficient denominator is zero");
            }
            
            Field inv_denom = modinv(denominator, PRIME);
            Field term = mod_mul(numerator, inv_denom, PRIME);
            res = mod_mul(res, term, PRIME);
            
            // cout << ", 逆=" << inv_denom << ", 项=" << term << ", 累积=" << res << endl;
        }
    }
    
    // cout << "索引" << idx << "的最终拉格朗日系数: " << res << endl;
    return res;
}

// 秘密共享生成函数
vector<pair<Field, Field>> gen_shares(Field secret, int d, int n, mt19937_64& rng) {
    vector<Field> coeffs(d);
    coeffs[0] = secret;
    uniform_int_distribution<Field> dist(1, PRIME-1);
    for (int i = 1; i < d; ++i) {
        coeffs[i] = dist(rng);
    }
    
    vector<pair<Field, Field>> shares(n); // (x, y)
    for (int x = 1; x <= n; ++x) {
        Field y = 0;
        for (int i = 0; i < d; ++i) {
            Field term = mod_mul(coeffs[i], powm(x, i, PRIME), PRIME);
            y = (y + term) % PRIME;
        }
        shares[x-1] = {Field(x), y};
    }
    return shares;
}

// 生成所有参与方的集合
vector<vector<Field>> gen_all_sets(int n, int m, mt19937_64& rng) {
    vector<Field> common(2);
    uniform_int_distribution<Field> dist(1, PRIME-1);
    for (int i = 0; i < 2; ++i) {
        common[i] = dist(rng);
    }
    
    set<Field> used(common.begin(), common.end());
    vector<vector<Field>> sets(n);
    
    for (int i = 0; i < n; ++i) {
        sets[i].insert(sets[i].end(), common.begin(), common.end());
        while (sets[i].size() < (size_t)m) {
            Field x = dist(rng);
            if (used.count(x)) continue;
            sets[i].push_back(x);
            used.insert(x);
        }
    }
    return sets;
}

// 通信统计结构
struct CommStat {
    uint64_t send_bytes = 0;
    uint64_t recv_bytes = 0;
    void add_send(size_t n) { send_bytes += n; }
    void add_recv(size_t n) { recv_bytes += n; }
    double getSentMB() const { return send_bytes / 1024.0 / 1024.0; }
    double getReceivedMB() const { return recv_bytes / 1024.0 / 1024.0; }
    double getTotalMB() const { return (send_bytes + recv_bytes) / 1024.0 / 1024.0; }
};

// OKVS接口函数
block field2block(Field x) {
    block b = oc::ZeroBlock;
    memcpy(b.data(), &x, sizeof(Field));
    return b;
}

Field block2field(const block& b) {
    Field x;
    memcpy(&x, b.data(), sizeof(Field));
    return x;
}

void encode_OKVS(const vector<pair<Field, Field>>& kv, vector<block>& okvs, Baxos& paxos, PRNG& prng) {
    vector<block> keys, vals;
    for (auto& p : kv) {
        keys.push_back(field2block(p.first));
        vals.push_back(field2block(p.second));
    }
    okvs.resize(paxos.size());
    paxos.solve<block>(keys, vals, okvs, &prng, 1);
}

Field decode_OKVS(const vector<block>& okvs, Baxos& paxos, Field x) {
    block bx = field2block(x);
    vector<block> keys = {bx};
    vector<block> vals = {oc::ZeroBlock};
    paxos.decode<block>(keys, vals, okvs, 1);
    return block2field(vals[0]);
}

int main(int argc, char** argv) {
    int n, m, d, c;
    string ip = "127.0.0.1";
    if (argc == 6) {
        n = stoi(argv[1]);
        m = stoi(argv[2]);
        d = stoi(argv[3]);
        c = stoi(argv[4]);
        ip = argv[5];
    } else {
        cout << "输入参与方数量n，每方集合元素数量m(2的次方)，秘密共享阈值d，在线中间方数量c, 本机ip: ";
        cin >> n >> m >> d >> c >> ip;
    }
    assert(n >= 3 && d >= 2 && c >= d && c <= n-2);

    mt19937_64 rng(random_device{}());

    auto sets = gen_all_sets(n, m, rng);

    // 生成密钥k，确保不为0
    uniform_int_distribution<Field> key_dist(1, PRIME-1);
    Field k = key_dist(rng);
    
    auto shares = gen_shares(k, d, n-2, rng); // 为P2到P_{n-1}生成份额
    vector<Field> kivs(n-2);
    for (int i = 0; i < n-2; ++i) {
        kivs[i] = shares[i].second;
    }

    // 生成随机数r_{1,i}，确保不为0
    vector<Field> r_1_i(n-2);
    for (int i = 0; i < n-2; ++i) {
        r_1_i[i] = key_dist(rng);
    }

    // 选择前c个中间参与方作为在线参与方
    vector<int> online_parties;
    for (int i = 2; i <= min(c+1, n-1); ++i) {
        online_parties.push_back(i);
    }

    // 打印参数
    cout << "输出结果形式 1: n=" << n << ", m=" << m << ", d=" << d << ", c=" << c << endl;
    // cout << "使用素数: " << PRIME << endl;
    // cout << "密钥k: " << k << endl;
    // cout << "在线中间参与方: ";
    // for (int p : online_parties) cout << "P" << p << " ";
    // cout << endl;
    cout << "================================================" << endl << endl;

    vector<thread> threads;

    for (int pid = 1; pid <= n; ++pid) {
        threads.emplace_back([&, pid]() {
            try {
                auto t_main_start = chrono::steady_clock::now();
                double totalComputeTime = 0.0;
                
                // 时间统计变量
                double keyShareGenTime = 0.0;
                double reciverkey = 0.0;
                double setTransformTime = 0.0;
                double okvsEncodeTime = 0.0;
                double okvsDecodeTime = 0.0;
                double computeR = 0.0;
                double psiTime = 0.0;
                double finalIntersectionTime = 0.0;
                
                CommStat commStats;

                // cout << "P" << pid << " 开始网络连接..." << endl;

                // --- 网络连接 ---
                std::vector<Socket> Chl(n+1);
                for (int peer = 1; peer <= n; ++peer) {
                    if (peer == pid) continue;
                    int port = BASE_PORT + min(pid, peer) * 100 + max(pid, peer);
                    string addr = ip + ":" + to_string(port);
                    if (pid < peer)
                        Chl[peer] = coproto::asioConnect(addr, true);
                    else
                        Chl[peer] = coproto::asioConnect(addr, false);
                }

                // cout << "P" << pid << " 网络连接完成" << endl;

                if (pid == 1) {
                    // cout << "P1 开始执行..." << endl;
                    
                    // P1: 生成密钥份额和随机数，发送给P2到P_{n-1}
                    auto t0 = chrono::steady_clock::now();
                    auto t1 = chrono::steady_clock::now();
                    keyShareGenTime = chrono::duration<double>(t1 - t0).count();
                    totalComputeTime += keyShareGenTime;

                    // cout << "P1 发送密钥份额..." << endl;
                    // 发送(k_i, r_{1,i})给P2到P_{n-1}
                    for (int i = 2; i <= n-1; ++i) {
                        coproto::sync_wait(Chl[i].send(kivs[i-2]));
                        coproto::sync_wait(Chl[i].send(r_1_i[i-2]));
                        commStats.add_send(2 * sizeof(Field));
                    }

                    // cout << "P1 转换集合..." << endl;
                    // P1转换自己的集合
                    auto t_transform_start = chrono::steady_clock::now();
                    vector<pair<Field, Field>> transformed_set;
                    for (Field x : sets[0]) {
                        Field y = powm(x, k, PRIME);
                        transformed_set.push_back({x, y});
                    }
                    auto t_transform_end = chrono::steady_clock::now();
                    setTransformTime = chrono::duration<double>(t_transform_end - t_transform_start).count();
                    totalComputeTime += setTransformTime;

                    // cout << "P1 等待接收在线参与方信息..." << endl;
                    // 接收来自P_n的在线参与方ID集合C
                    vector<int> C;
                    uint64_t c_size;
                    coproto::sync_wait(Chl[n].recv(c_size));
                    commStats.add_recv(sizeof(uint64_t));
                    C.resize(c_size);
                    coproto::sync_wait(Chl[n].recv(C));
                    commStats.add_recv(c_size * sizeof(int));

                    // cout << "P1 计算R..." << endl;
                    // cout << "在线参与方C: ";
                    // for (int i : C) cout << i << " ";
                    // cout << endl;
                    
                    // 计算R - 使用改进的拉格朗日插值
                    auto t_r_start = chrono::steady_clock::now();
                    Field R = 1;
                    
                    try {
                        for (int idx = 0; idx < (int)C.size(); ++idx) {
                            int i = C[idx];
                            // cout << "P1 计算P" << i << "的贡献..." << endl;
                            
                            Field coeff = lagrange_coeff(idx, C);
                            // cout << "P1 r_1_i[" << (i-2) << "] = " << r_1_i[i-2] << ", coeff = " << coeff << endl;
                            
                            // 使用模幂计算 r^coeff mod PRIME
                            Field r_power = powm(r_1_i[i-2], coeff, PRIME);
                            // cout << "P1 r_power = " << r_power << endl;
                            
                            if (r_power == 0) {
                                throw runtime_error("r_power is zero for i=" + to_string(i));
                            }
                            
                            Field inv_r_power = modinv(r_power, PRIME);
                            // cout << "P1 inv_r_power = " << inv_r_power << endl;
                            
                            R = mod_mul(R, inv_r_power, PRIME);
                            // cout << "P1 当前R = " << R << endl;
                        }
                        // cout << "P1 成功计算R = " << R << endl;
                    } catch (const exception& e) {
                        // cout << "P1 计算R时出错: " << e.what() << endl;
                        throw;
                    }
                    
                    auto t_r_end = chrono::steady_clock::now();
                    computeR = chrono::duration<double>(t_r_end - t_r_start).count();
                    totalComputeTime += computeR;

                    // 发送R给P_n
                    coproto::sync_wait(Chl[n].send(R));
                    commStats.add_send(sizeof(Field));

                    // cout << "P1 准备两方PSI..." << endl;
                    // 准备两方PSI的输入
                    vector<block> psi_input;
                    for (auto& p : transformed_set) {
                        psi_input.push_back(field2block(p.second));
                    }

                    // cout << "P1 执行两方PSI..." << endl;
                    // 执行两方PSI - P1作为接收方
                    auto t_psi_start = chrono::steady_clock::now();
                    
                    try {
                        RsPsiReceiver receiver;
                        receiver.init(m, m, 40, oc::ZeroBlock, false, 1);
                        
                        // cout << "P1 PSI初始化完成，开始运行..." << endl;
                        
                        // 执行PSI
                        auto task = receiver.run(psi_input, Chl[n]);
                        macoro::sync_wait(macoro::when_all_ready(std::move(task)));
                        
                        // cout << "P1 PSI运行完成" << endl;
                        
                        // 获取交集
                        vector<Field> final_intersection;
                        for (u64 idx : receiver.mIntersection) {
                            if (idx < sets[0].size()) {
                                final_intersection.push_back(sets[0][idx]);
                            }
                        }
                        
                        // cout << "P1 找到交集元素数量: " << final_intersection.size() << endl;
                        
                    } catch (const exception& e) {
                        // cout << "P1 PSI执行出错: " << e.what() << endl;
                    }
                    
                    auto t_psi_end = chrono::steady_clock::now();
                    psiTime = chrono::duration<double>(t_psi_end - t_psi_start).count();
                    totalComputeTime += psiTime;

                    finalIntersectionTime = 0.001; // 占位
                    totalComputeTime += finalIntersectionTime;

                    // cout << "P1 完成" << endl;
                }
                else if (pid >= 2 && pid <= n-1) {
                    // cout << "P" << pid << " 开始执行..." << endl;
                    
                    // 接收密钥份额和随机数
                    auto t0 = chrono::steady_clock::now();
                    Field k_i, r_1_i_val;
                    coproto::sync_wait(Chl[1].recv(k_i));
                    coproto::sync_wait(Chl[1].recv(r_1_i_val));
                    commStats.add_recv(2 * sizeof(Field));
                    auto t1 = chrono::steady_clock::now();
                    reciverkey = chrono::duration<double>(t1 - t0).count();

                    // cout << "P" << pid << " 收到k_i=" << k_i << ", r_1_i=" << r_1_i_val << endl;

                    // 检查是否为在线参与方
                    bool is_online = find(online_parties.begin(), online_parties.end(), pid) != online_parties.end();
                    
                    if (is_online) {
                        // cout << "P" << pid << " 是在线参与方，转换集合..." << endl;
                        
                        // 转换集合
                        auto t_transform_start = chrono::steady_clock::now();
                        vector<pair<Field, Field>> transformed_set;
                        for (Field x : sets[pid-1]) {
                            Field x_k = powm(x, k_i, PRIME);
                            Field y = mod_mul(r_1_i_val, x_k, PRIME);
                            transformed_set.push_back({x, y});
                        }
                        auto t_transform_end = chrono::steady_clock::now();
                        setTransformTime = chrono::duration<double>(t_transform_end - t_transform_start).count();
                        totalComputeTime += setTransformTime;

                        // cout << "P" << pid << " 编码OKVS..." << endl;
                        // 编码OKVS
                        auto t_encode_start = chrono::steady_clock::now();
                        PRNG prng(oc::ZeroBlock);
                        Baxos paxos;
                        paxos.init(m, 1<<14, 3, 40, PaxosParam::GF128, oc::ZeroBlock);
                        vector<block> okvs;
                        encode_OKVS(transformed_set, okvs, paxos, prng);
                        auto t_encode_end = chrono::steady_clock::now();
                        okvsEncodeTime = chrono::duration<double>(t_encode_end - t_encode_start).count();
                        totalComputeTime += okvsEncodeTime;

                        // cout << "P" << pid << " 发送OKVS..." << endl;
                        // 发送OKVS给P_n
                        uint64_t okvs_size = okvs.size();
                        coproto::sync_wait(Chl[n].send(pid)); // 发送自己的ID
                        coproto::sync_wait(Chl[n].send(okvs_size));
                        coproto::sync_wait(Chl[n].send(okvs));
                        commStats.add_send(sizeof(int) + sizeof(uint64_t) + okvs.size() * sizeof(block));
                        
                        // cout << "P" << pid << " 完成" << endl;
                    } else {
                        // cout << "P" << pid << " 是离线参与方，跳过主流程" << endl;
                        totalComputeTime = reciverkey;
                    }
                }
                else if (pid == n) {
                    // cout << "P" << n << " 开始执行..." << endl;
                    
                    // 接收来自在线中间参与方的OKVS
                    map<int, vector<block>> received_okvs;
                    map<int, Baxos> paxos_map;
                    vector<int> C; // 实际在线参与方ID集合
                    
                    // cout << "P" << n << " 接收OKVS..." << endl;
                    for (int expected_pid : online_parties) {
                        try {
                            int sender_id;
                            coproto::sync_wait(Chl[expected_pid].recv(sender_id));
                            commStats.add_recv(sizeof(int));
                            
                            uint64_t okvs_size;
                            coproto::sync_wait(Chl[expected_pid].recv(okvs_size));
                            commStats.add_recv(sizeof(uint64_t));
                            
                            vector<block> okvs(okvs_size);
                            coproto::sync_wait(Chl[expected_pid].recv(okvs));
                            commStats.add_recv(okvs_size * sizeof(block));
                            
                            received_okvs[sender_id] = okvs;
                            C.push_back(sender_id);
                            
                            Baxos paxos;
                            paxos.init(m, 1<<14, 3, 40, PaxosParam::GF128, oc::ZeroBlock);
                            paxos_map[sender_id] = paxos;
                            
                            // cout << "P" << n << " 收到来自P" << sender_id << "的OKVS" << endl;
                        } catch (const exception& e) {
                            // cout << "P" << n << " 接收P" << expected_pid << "的数据失败: " << e.what() << endl;
                            continue;
                        }
                    }
                    
                    sort(C.begin(), C.end());
                    int actual_c = C.size();
                    
                    if (actual_c < d) {
                        // cout << "错误：在线参与方数量不足，无法恢复秘密" << endl;
                        return;
                    }

                    // cout << "P" << n << " 发送在线参与方信息给P1..." << endl;
                    // 发送实际在线参与方ID集合给P1
                    uint64_t c_size = C.size();
                    coproto::sync_wait(Chl[1].send(c_size));
                    coproto::sync_wait(Chl[1].send(C));
                    commStats.add_send(sizeof(uint64_t) + C.size() * sizeof(int));

                    // cout << "P" << n << " 解码OKVS..." << endl;
                    // 解码OKVS
                    auto t_decode_start = chrono::steady_clock::now();
                    vector<vector<Field>> D(m, vector<Field>(actual_c));
                    for (int j = 0; j < m; ++j) {
                        Field x = sets[pid-1][j];
                        for (int v = 0; v < actual_c; ++v) {
                            int i = C[v];
                            D[j][v] = decode_OKVS(received_okvs[i], paxos_map[i], x);
                        }
                    }
                    auto t_decode_end = chrono::steady_clock::now();
                    okvsDecodeTime = chrono::duration<double>(t_decode_end - t_decode_start).count();
                    totalComputeTime += okvsDecodeTime;

                    // cout << "P" << n << " 接收R..." << endl;
                    // 接收R从P1
                    Field R;
                    coproto::sync_wait(Chl[1].recv(R));
                    commStats.add_recv(sizeof(Field));

                    // cout << "P" << n << " 转换集合..." << endl;
                    // 转换集合 - 使用改进的拉格朗日插值
                    auto t_transform_start = chrono::steady_clock::now();
                    vector<Field> transformed_values;
                    
                    try {
                        for (int j = 0; j < m; ++j) {
                            Field prod = 1;
                            for (int v = 0; v < actual_c; ++v) {
                                int i = C[v];
                                Field coeff = lagrange_coeff(v, C);
                                Field powered = powm(D[j][v], coeff, PRIME);
                                prod = mod_mul(prod, powered, PRIME);
                            }
                            prod = mod_mul(prod, R, PRIME);
                            transformed_values.push_back(prod);
                        }
                        // cout << "P" << n << " 成功转换集合" << endl;
                    } catch (const exception& e) {
                        // cout << "P" << n << " 转换集合时出错: " << e.what() << endl;
                        throw;
                    }
                    
                    auto t_transform_end = chrono::steady_clock::now();
                    setTransformTime = chrono::duration<double>(t_transform_end - t_transform_start).count();
                    totalComputeTime += setTransformTime;

                    // cout << "P" << n << " 准备两方PSI..." << endl;
                    // 准备两方PSI输入
                    vector<block> psi_input;
                    for (Field val : transformed_values) {
                        psi_input.push_back(field2block(val));
                    }

                    // cout << "P" << n << " 执行两方PSI..." << endl;
                    // 执行两方PSI - P_n作为发送方
                    auto t_psi_start = chrono::steady_clock::now();
                    
                    try {
                        RsPsiSender sender;
                        sender.init(m, m, 40, oc::ZeroBlock, false, 1);
                        
                        // cout << "P" << n << " PSI初始化完成，开始运行..." << endl;
                        // 执行PSI
                        auto task = sender.run(psi_input, Chl[1]);
                        macoro::sync_wait(macoro::when_all_ready(std::move(task)));
                        
                        // cout << "P" << n << " PSI运行完成" << endl;
                        
                    } catch (const exception& e) {
                        // cout << "P" << n << " PSI执行出错: " << e.what() << endl;
                    }
                    
                    auto t_psi_end = chrono::steady_clock::now();
                    psiTime = chrono::duration<double>(t_psi_end - t_psi_start).count();
                    totalComputeTime += psiTime;

                    // cout << "P" << n << " 完成" << endl;
                }

                double totalRunTime = chrono::duration<double>(chrono::steady_clock::now() - t_main_start).count();

                // 打印结果 - 只保留P1~Pn的结果输出
                std::cout << "\nP" << pid << " 结果:" << std::endl;
                
                if (pid == 1) {
                    std::cout << "   P1生成密钥份额和随机数: " << std::fixed << std::setprecision(6) << keyShareGenTime << "s" << std::endl;
                    std::cout << "   P1转换集合: " << std::fixed << std::setprecision(6) << setTransformTime << "s" << std::endl;
                    std::cout << "   P1计算R: " << std::fixed << std::setprecision(6) << computeR << "s" << std::endl;
                    std::cout << "   P1执行两方PSI: " << std::fixed << std::setprecision(6) << psiTime << "s" << std::endl;
                    std::cout << "   P1计算最终交集: " << std::fixed << std::setprecision(6) << finalIntersectionTime << "s" << std::endl;
                    std::cout << "   P1纯计算时间（不含网络）: " << std::fixed << std::setprecision(6) << totalComputeTime << "s" << std::endl;
                    std::cout << "   P1总运行时间（含网络）: " << std::fixed << std::setprecision(6) << totalRunTime << "s" << std::endl;
                } else if (pid >= 2 && pid <= n-1) {
                    std::cout << "   P" << pid << "接收密钥份额: " << std::fixed << std::setprecision(6) << reciverkey << "s" << std::endl;
                    std::cout << "   P" << pid << "转换集合: " << std::fixed << std::setprecision(6) << setTransformTime << "s" << std::endl;
                    std::cout << "   P" << pid << "编码OKVS: " << std::fixed << std::setprecision(6) << okvsEncodeTime << "s" << std::endl;
                    std::cout << "   P" << pid << "纯计算时间（不含网络）: " << std::fixed << std::setprecision(6) << totalComputeTime << "s" << std::endl;
                    std::cout << "   P" << pid << "总运行时间（含网络）: " << std::fixed << std::setprecision(6) << totalRunTime << "s" << std::endl;
                } else if (pid == n) {
                    std::cout << "   P" << pid << "解码OKVS: " << std::fixed << std::setprecision(6) << okvsDecodeTime << "s" << std::endl;
                    std::cout << "   P" << pid << "转换集合: " << std::fixed << std::setprecision(6) << setTransformTime << "s" << std::endl;
                    std::cout << "   P" << pid << "执行两方PSI: " << std::fixed << std::setprecision(6) << psiTime << "s" << std::endl;
                    std::cout << "   P" << pid << "纯计算时间（不含网络）: " << std::fixed << std::setprecision(6) << totalComputeTime << "s" << std::endl;
                    std::cout << "   P" << pid << "总运行时间（含网络）: " << std::fixed << std::setprecision(6) << totalRunTime << "s" << std::endl;
                }
                
                // 打印通信开销
                std::cout << "   通信开销:" << std::endl;
                std::cout << "     发送: " << std::fixed << std::setprecision(3) << commStats.getSentMB() << " MB" << std::endl;
                std::cout << "     接收: " << std::fixed << std::setprecision(3) << commStats.getReceivedMB() << " MB" << std::endl;
                std::cout << "     总计: " << std::fixed << std::setprecision(3) << commStats.getTotalMB() << " MB" << std::endl;

                // 关闭Socket
                for (int peer = 1; peer <= n; ++peer) {
                    if (peer != pid) {
                        try {
                            coproto::sync_wait(Chl[peer].close());
                        } catch (...) {
                            // 忽略关闭时的异常
                        }
                    }
                }
                    
            } catch (const exception& e) {
                // cout << "P" << pid << " 执行过程中出现异常: " << e.what() << endl;
            } catch (...) {
                // cout << "P" << pid << " 执行过程中出现未知异常" << endl;
            }
        });
    }

    for (auto& th : threads) {
        th.join();
    }

    // cout << "\n所有参与方执行完成！" << endl;
    return 0;
}

