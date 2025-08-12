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

#include "volePSI/Mpsi.h"
#include "volePSI/SimpleIndex.h"
#include "volePSI/Defines.h"
#include "coproto/Socket/AsioSocket.h"
#include <cryptoTools/Common/Timer.h>
#include <cryptoTools/Crypto/PRNG.h>
#include <cryptoTools/Crypto/RandomOracle.h>
#include <cryptoTools/Common/BitVector.h>
#include <cryptoTools/Crypto/SodiumCurve.h>

using namespace std;
using namespace volePSI;
using namespace oc;
using coproto::Socket;

#define BASE_PORT 12000

using Field = uint64_t;
const Field PRIME = 0xFFFFFFFF00000001ULL; // 64位大素数

Field modinv(Field a, Field p = PRIME) {
    Field t = 0, newt = 1, r = p, newr = a;
    while (newr != 0) {
        Field q = r / newr;
        t = t - q * newt; swap(t, newt);
        r = r - q * newr; swap(r, newr);
    }
    if (r > 1) throw runtime_error("a not invertible");
    if (t < 0) t += p;
    return t;
}

uint64_t powm(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1)
            result = (result * base) % mod;
        base = (base * base) % mod;
        exp >>= 1;
    }
    return result;
}

Field lagrange_coeff(int idx, const vector<int>& C) {
    Field res = 1;
    int i_v = C[idx];
    for (int l : C) if (l != i_v) {
        res = res * ((PRIME - l) % PRIME) % PRIME;
        res = res * modinv((i_v - l + PRIME) % PRIME) % PRIME;
    }
    return res;
}

vector<pair<Field, Field>> gen_shares(Field secret, int d, int n, mt19937_64& rng) {
    vector<Field> coeffs(d);
    coeffs[0] = secret;
    uniform_int_distribution<Field> dist(1, PRIME-1);
    for (int i = 1; i < d; ++i) coeffs[i] = dist(rng);
    vector<pair<Field, Field>> shares(n); // (x, y)
    for (int x = 1; x <= n; ++x) {
        Field y = 0;
        for (int i = 0; i < d; ++i)
            y = (y + coeffs[i] * powm(x, i, PRIME)) % PRIME;
        shares[x-1] = {Field(x), y};
    }
    return shares;
}

vector<vector<Field>> gen_all_sets(int n, int m, mt19937_64& rng) {
    vector<Field> common(2);
    uniform_int_distribution<Field> dist(1, PRIME-1);
    for (int i = 0; i < 2; ++i) common[i] = dist(rng);
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

struct CommStat {
    uint64_t send_bytes = 0;
    uint64_t recv_bytes = 0;
    void add_send(size_t n) { send_bytes += n; }
    void add_recv(size_t n) { recv_bytes += n; }
    double mb_send() const { return send_bytes / 1024.0 / 1024.0; }
    double mb_recv() const { return recv_bytes / 1024.0 / 1024.0; }
    double mb_total() const { return (send_bytes + recv_bytes) / 1024.0 / 1024.0; }
};

vector<map<pair<int,int>, Field>> exchange_masks(const vector<int>& online_ids, int my_id, int idx_in_C, int c, vector<Socket>& Chl, CommStat& comm, mt19937_64& rng) {
    vector<map<pair<int,int>, Field>> all_masks(c);
    for (int v = 0; v < c; ++v) {
        int id_v = online_ids[v];
        for (int j = v+1; j < c; ++j) {
            int id_j = online_ids[j];
            if (my_id == id_v) {
                uniform_int_distribution<Field> dist(1, PRIME-1);
                Field r = dist(rng);
                coproto::sync_wait(Chl[id_j].send(r));
                comm.add_send(sizeof(Field));
                all_masks[v][{id_v, id_j}] = r;
            }
            if (my_id == id_j) {
                Field r;
                coproto::sync_wait(Chl[id_v].recv(r));
                comm.add_recv(sizeof(Field));
                all_masks[j][{id_v, id_j}] = r;
            }
        }
    }
    return all_masks;
}

vector<pair<Field, Field>> transform_set(const vector<Field>& set, int my_id, int idx_in_C, const vector<int>& C, Field k_iv, const map<pair<int,int>, Field>& my_masks) {
    vector<pair<Field, Field>> res;
    Field lag = lagrange_coeff(idx_in_C, C);
    for (Field x : set) {
        Field mask = 1;
        for (int u : C) if (u < my_id) {
            auto it = my_masks.find({u, my_id});
            if (it != my_masks.end()) mask = mask * it->second % PRIME;
        }
        for (int j : C) if (j > my_id) {
            auto it = my_masks.find({my_id, j});
            if (it != my_masks.end()) mask = mask * modinv(it->second) % PRIME;
        }
        Field exp = (k_iv * lag) % (PRIME-1); // 指数应模p-1
        Field val = mask * powm(x, exp, PRIME) % PRIME;
        res.push_back({x, val});
    }
    return res;
}

// OKVS接口
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
    block bv;
    vector<block> keys = {bx};
    vector<block> vals = {oc::ZeroBlock};
    paxos.decode<block>(keys, vals, okvs, 1);
    return block2field(vals[0]);
}

struct PartyStat {
    // 纯计算时间统计
    double key_gen_time = 0;          // 密钥生成时间
    double mask_gen_time = 0;         // 掩码生成时间
    double transform_time = 0;        // 集合转换时间
    double encode_time = 0;           // OKVS编码时间
    double decode_time = 0;           // OKVS解码时间
    double intersection_time = 0;     // 交集计算时间
    double pure_compute_time = 0;     // 纯计算时间总和
    
    // 总运行时间
    double total_time = 0;
    
    CommStat comm;
    vector<Field> output;
    
    void calculate_pure_compute_time() {
        pure_compute_time = key_gen_time + mask_gen_time + transform_time + 
                           encode_time + decode_time + intersection_time;
    }
};

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
    assert(n >= 3 && d >= 2 && c >= d && c <= n-1);

    mt19937_64 rng(random_device{}());

    auto sets = gen_all_sets(n, m, rng);

    Field k = rng() % PRIME;
    auto shares = gen_shares(k, d, n-1, rng); // x=1,2,...,n-1
    vector<Field> kivs(n-1);
    for (int i = 0; i < n-1; ++i) kivs[i] = shares[i].second;

    vector<int> mids;
    for (int i = 2; i <= n; ++i) mids.push_back(i);
    shuffle(mids.begin(), mids.end(), rng);
    vector<int> C(mids.begin(), mids.begin()+c);
    sort(C.begin(), C.end());

    // 打印参数
    cout << "输出结果形式 1: n=" << n << ", m=" << m << ", d=" << d << ", c=" << c << endl;
    cout << "================================================" << endl << endl;

    vector<PartyStat> stats(n+1); // 1-based
    vector<thread> threads;

    for (int pid = 1; pid <= n; ++pid) {
        threads.emplace_back([&, pid]() {
            auto t_main_start = chrono::steady_clock::now();

            PartyStat& stat = stats[pid];
            CommStat& comm = stat.comm;

            // --- 1. 网络连接 ---
            std::vector<Socket> Chl(n+1);
            for (int peer = 1; peer <= n; ++peer) {
                if (peer == pid) continue;
                int port = BASE_PORT + min(pid, peer) * 100 + max(pid, peer);
                string addr = ip + ":" + to_string(port);
                // 低编号listen, 高编号connect
                if (pid < peer)
                    Chl[peer] = coproto::asioConnect(addr, true);  // listen
                else
                    Chl[peer] = coproto::asioConnect(addr, false); // connect
            }

            if (pid == 1) {
                // P1生成密钥份额和随机数
                auto t_key_start = chrono::steady_clock::now();
                // kivs 已经生成
                auto t_key_end = chrono::steady_clock::now();
                stat.key_gen_time = chrono::duration<double>(t_key_end - t_key_start).count();

                // 发送份额 (网络通信，不计入纯计算时间)
                vector<thread> send_thrds;
                for (int party_id : C) { 
                    send_thrds.emplace_back([&, party_id]() {
                        coproto::sync_wait(Chl[party_id].send(kivs[party_id - 2]));
                        comm.add_send(sizeof(Field));
                    });
                }
                for (auto& th : send_thrds) th.join();

                // 接收OKVS (网络通信，不计入纯计算时间)
                vector<vector<block>> all_okvs;
                vector<Baxos> all_paxos;
                vector<int> idx_in_C;
                vector<uint64_t> okvs_sizes(c);
                vector<vector<block>> okvs_vecs(c);

                vector<thread> recv_thrds;
                for (int v = 0; v < c; ++v) {
                    int i_v = C[v];
                    recv_thrds.emplace_back([&, v, i_v]() {
                        uint64_t okvs_size = 0;
                        coproto::sync_wait(Chl[i_v].recv(okvs_size));
                        comm.add_recv(sizeof(uint64_t));
                        okvs_sizes[v] = okvs_size;
                    });
                }
                for (auto& th : recv_thrds) th.join();

                recv_thrds.clear();
                for (int v = 0; v < c; ++v) {
                    int i_v = C[v];
                    okvs_vecs[v].resize(okvs_sizes[v]);
                    recv_thrds.emplace_back([&, v, i_v]() {
                        coproto::sync_wait(Chl[i_v].recv(okvs_vecs[v]));
                        comm.add_recv(okvs_sizes[v] * sizeof(block));
                    });
                }
                for (auto& th : recv_thrds) th.join();

                // 初始化OKVS解码器 (纯计算)
                auto t_decode_setup_start = chrono::steady_clock::now();
                for (int v = 0; v < c; ++v) {
                    Baxos paxos;
                    paxos.init(m, 1<<14, 3, 40, PaxosParam::GF128, oc::ZeroBlock);
                    all_okvs.push_back(okvs_vecs[v]);
                    all_paxos.push_back(paxos);
                    idx_in_C.push_back(v);
                }
                auto t_decode_setup_end = chrono::steady_clock::now();
                stat.decode_time += chrono::duration<double>(t_decode_setup_end - t_decode_setup_start).count();

                // 计算交集 (纯计算)
                auto t_intersection_start = chrono::steady_clock::now();
                vector<Field> myset = sets[0];
                vector<Field> intersection;
                for (Field x : myset) {
                    vector<Field> vals;
                    for (int v = 0; v < c; ++v) {
                        Field val = decode_OKVS(all_okvs[v], all_paxos[v], x);
                        vals.push_back(val);
                    }
                    Field prod = 1;
                    for (Field v : vals) prod = prod * v % PRIME;
                    if (prod == powm(x, k, PRIME)) intersection.push_back(x);
                }
                auto t_intersection_end = chrono::steady_clock::now();
                stat.intersection_time = chrono::duration<double>(t_intersection_end - t_intersection_start).count();

                stat.output = intersection;
            }
            else if (find(C.begin(), C.end(), pid) != C.end()) {
                int idx = find(C.begin(), C.end(), pid) - C.begin();
                
                // 接收密钥份额 (网络通信，不计入纯计算时间)
                Field k_iv = 0;
                coproto::sync_wait(Chl[1].recv(k_iv));
                comm.add_recv(sizeof(Field));

                // 生成随机掩码 (纯计算)
                auto t_mask_start = chrono::steady_clock::now();
                mt19937_64 local_rng(rng());
                auto t_mask_end = chrono::steady_clock::now();
                stat.mask_gen_time = chrono::duration<double>(t_mask_end - t_mask_start).count();

                // 交换mask (网络通信，不计入纯计算时间)
                auto masks = exchange_masks(C, pid, idx, c, Chl, comm, local_rng);

                // 转换集合 (纯计算)
                auto t_transform_start = chrono::steady_clock::now();
                auto kv = transform_set(sets[pid-1], pid, idx, C, k_iv, masks[idx]);
                auto t_transform_end = chrono::steady_clock::now();
                stat.transform_time = chrono::duration<double>(t_transform_end - t_transform_start).count();

                // 编码OKVS (纯计算)
                auto t_encode_start = chrono::steady_clock::now();
                PRNG prng(oc::ZeroBlock);
                Baxos paxos;
                paxos.init(kv.size(), 1<<14, 3, 40, PaxosParam::GF128, oc::ZeroBlock);
                vector<block> okvs;
                encode_OKVS(kv, okvs, paxos, prng);
                auto t_encode_end = chrono::steady_clock::now();
                stat.encode_time = chrono::duration<double>(t_encode_end - t_encode_start).count();

                // 发送OKVS (网络通信，不计入纯计算时间)
                uint64_t okvs_size = okvs.size();
                coproto::sync_wait(Chl[1].send(okvs_size));
                comm.add_send(sizeof(uint64_t));
                coproto::sync_wait(Chl[1].send(okvs));
                comm.add_send(okvs.size()*sizeof(block));

                stat.output = sets[pid-1];
            }
            else {
                // 离线方
                stat.output = sets[pid-1];
            }

            // 计算纯计算时间总和
            stat.calculate_pure_compute_time();
            
            // 总运行时间
            stat.total_time = chrono::duration<double>(chrono::steady_clock::now() - t_main_start).count();

            // 关闭Socket
            for (int peer = 1; peer <= n; ++peer)
                if (peer != pid) coproto::sync_wait(Chl[peer].close());
        });
    }

    for (auto& th : threads) th.join();

    // 打印每个参与方的详细统计
    for (int pid = 1; pid <= n; ++pid) {
        PartyStat& stat = stats[pid];
        ostringstream oss;
        
        if (pid == 1) {
            oss << "P1 结果:\n";
            oss << "   纯计算时间分解:\n";
            oss << "     密钥生成: " << fixed << setprecision(6) << stat.key_gen_time << "s\n";
            oss << "     OKVS解码初始化: " << fixed << setprecision(6) << stat.decode_time << "s\n";
            oss << "     交集计算: " << fixed << setprecision(6) << stat.intersection_time << "s\n";
            oss << "   P1纯计算时间: " << fixed << setprecision(6) << stat.pure_compute_time << "s\n";
            oss << "   P1总运行时间: " << fixed << setprecision(6) << stat.total_time << "s\n";
        } 
        else if (find(C.begin(), C.end(), pid) != C.end()) {
            oss << "P" << pid << " 结果:\n";
            oss << "   纯计算时间分解:\n";
            oss << "     掩码生成: " << fixed << setprecision(6) << stat.mask_gen_time << "s\n";
            oss << "     集合转换: " << fixed << setprecision(6) << stat.transform_time << "s\n";
            oss << "     OKVS编码: " << fixed << setprecision(6) << stat.encode_time << "s\n";
            oss << "   P" << pid << "纯计算时间: " << fixed << setprecision(6) << stat.pure_compute_time << "s\n";
            oss << "   P" << pid << "总运行时间: " << fixed << setprecision(6) << stat.total_time << "s\n";
        } 
        else {
            oss << "P" << pid << " 结果:\n";
            oss << "   P" << pid << "为离线方，无参与主流程。\n";
            oss << "   P" << pid << "纯计算时间: " << fixed << setprecision(6) << stat.pure_compute_time << "s\n";
            oss << "   P" << pid << "总运行时间: " << fixed << setprecision(6) << stat.total_time << "s\n";
        }
        
        oss << "   通信开销:\n";
        oss << "     发送: " << fixed << setprecision(3) << stat.comm.mb_send() << " MB\n";
        oss << "     接收: " << fixed << setprecision(3) << stat.comm.mb_recv() << " MB\n";
        oss << "     总计: " << fixed << setprecision(3) << stat.comm.mb_total() << " MB\n";
        cout << oss.str() << endl;
    }
    
    return 0;
}
