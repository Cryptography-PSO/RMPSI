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


    return 0;
}

