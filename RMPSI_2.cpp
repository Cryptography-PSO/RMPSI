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

