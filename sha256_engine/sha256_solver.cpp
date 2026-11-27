#include <iostream>
#include <vector>
#include <cmath>
#include <chrono>
#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <cassert>
#include <thread>
#include <future>
#include <atomic>
#include <mutex>
#include <random>
#include <tuple>
#include <memory>
#include <cstring>
#include <fstream>

using namespace std;

// =====================================================================
// FIPS 180-4 / RFC 6234 (SHA-256) STANDARD CONSTANTS
// =====================================================================
const uint32_t K_SHA256[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

const uint32_t IV_SHA256[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

// SHA-256 standard bit operations
inline uint32_t rotr(uint32_t x, int n) { n &= 31; return n ? ((x >> n) | (x << (32 - n))) : x; }
inline uint32_t shr(uint32_t x, int n)  { return (x >> n); }

inline uint32_t sig0(uint32_t x) { return rotr(x, 7) ^ rotr(x, 18) ^ shr(x, 3); }
inline uint32_t sig1(uint32_t x) { return rotr(x, 17) ^ rotr(x, 19) ^ shr(x, 10); }
inline uint32_t Sig0(uint32_t x) { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
inline uint32_t Sig1(uint32_t x) { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
inline uint32_t Ch(uint32_t e, uint32_t f, uint32_t g) { return (e & f) ^ ((~e) & g); }
inline uint32_t Maj(uint32_t a, uint32_t b, uint32_t c) { return (a & b) ^ (a & c) ^ (b & c); }

// =====================================================================
// CLAUSE SHARING POOL (MULTITHREADING)
// =====================================================================
struct SharedClause {
    vector<int> lits;
    int lbd = 0;
    int origin_thread = -1;
};

class ClauseSharingPool {
public:
    mutex mtx;
    static constexpr size_t CAPACITY = 16384;
    vector<SharedClause> ring_buffer;
    uint64_t total_published = 0;

    ClauseSharingPool() : ring_buffer(CAPACITY) {}

    void publish(const vector<int>& c, int lbd, int thread_id) {
        if (c.size() <= 3 || lbd <= 2) {
            lock_guard<mutex> lock(mtx);
            ring_buffer[total_published % CAPACITY] = {c, lbd, thread_id};
            total_published++;
        }
    }

    void fetch(uint64_t& last_seen_rev, vector<SharedClause>& out, int my_thread_id) {
        lock_guard<mutex> lock(mtx);
        if (last_seen_rev >= total_published) return;

        uint64_t start_rev = (total_published - last_seen_rev > CAPACITY) 
                             ? (total_published - CAPACITY) 
                             : last_seen_rev;

        for (uint64_t rev = start_rev; rev < total_published; ++rev) {
            const auto& sc = ring_buffer[rev % CAPACITY];
            if (sc.origin_thread != my_thread_id) {
                out.push_back(sc);
            }
        }
        last_seen_rev = total_published;
    }

    size_t size() {
        lock_guard<mutex> lock(mtx);
        return min((size_t)total_published, CAPACITY);
    }

    uint64_t total() {
        lock_guard<mutex> lock(mtx);
        return total_published;
    }
};

// =====================================================================
// BINARY HEAP FOR VSIDS
// =====================================================================
class VarOrderHeap {
public:
    const vector<double>& activity;
    vector<int> heap;
    vector<int> heap_pos;

    VarOrderHeap(const vector<double>& act) : activity(act) {}

    void init(int n) {
        heap.clear();
        heap.push_back(0);
        heap_pos.assign(n + 1, 0);
        for (int v = 1; v <= n; ++v) {
            heap_pos[v] = (int)heap.size();
            heap.push_back(v);
        }
        for (int i = (int)heap.size() / 2; i >= 1; --i) down(i);
    }

    inline bool empty() const { return heap.size() <= 1; }

    inline void up(int i) {
        int v = heap[i];
        double act = activity[v];
        while (i > 1) {
            int p = i / 2;
            if (activity[heap[p]] >= act) break;
            heap[i] = heap[p];
            heap_pos[heap[i]] = i;
            i = p;
        }
        heap[i] = v;
        heap_pos[v] = i;
    }

    inline void down(int i) {
        int v = heap[i];
        double act = activity[v];
        int sz = (int)heap.size();
        while (2 * i < sz) {
            int child = 2 * i;
            if (child + 1 < sz && activity[heap[child + 1]] > activity[heap[child]]) {
                child++;
            }
            if (act >= activity[heap[child]]) break;
            heap[i] = heap[child];
            heap_pos[heap[i]] = i;
            i = child;
        }
        heap[i] = v;
        heap_pos[v] = i;
    }

    inline void update(int v) {
        if (heap_pos[v] > 0) up(heap_pos[v]);
    }

    inline void insert(int v) {
        if (heap_pos[v] == 0) {
            heap_pos[v] = (int)heap.size();
            heap.push_back(v);
            up(heap_pos[v]);
        }
    }

    inline int pop_max() {
        if (empty()) return 0;
        int top_var = heap[1];
        heap_pos[top_var] = 0;
        int last_var = heap.back();
        heap.pop_back();
        if (heap.size() > 1) {
            heap[1] = last_var;
            heap_pos[last_var] = 1;
            down(1);
        }
        return top_var;
    }
};

// =====================================================================
// CLAUSE AND WATCHER STRUCTURES
// =====================================================================
struct Clause {
    vector<int> lits;
    bool learned;
    bool deleted;
    int lbd;
    int w1;
    int w2;
    Clause() : learned(false), deleted(false), lbd(0), w1(0), w2(0) {}
    Clause(const vector<int>& l, bool lrn = false, int l_val = 0)
        : lits(l), learned(lrn), deleted(false), lbd(l_val), w1(0), w2(l.size() > 1 ? 1 : 0) {}
};

struct Watcher {
    int c_idx;
    int blocker;
};

struct BinWatcher {
    int c_idx;
    int other_lit;
};

// =====================================================================
// FAST, VERIFIED CDCL SOLVER FOR CRYPTANALYSIS
// =====================================================================
class VerifiedCDCL {
public:
    int num_vars;
    vector<Clause> clauses;
    vector<vector<Watcher>> watches;
    vector<vector<BinWatcher>> bin_watches;
    int offset;

    vector<int8_t> assigns;
    vector<int> var_level;
    vector<int> var_reason;
    vector<int8_t> saved_phase;

    vector<int> trail;
    vector<int> trail_lim;
    int prop_head;

    vector<double> activity;
    double var_inc;
    double var_decay;
    VarOrderHeap order_heap;

    uint64_t conflicts;
    uint64_t decisions;
    uint64_t propagations;

    int seed;
    mt19937 rng;
    bool root_unsat = false;
    uint64_t restart_base;
    uint64_t luby_u;
    uint64_t luby_v;

    ClauseSharingPool* shared_pool;
    uint64_t shared_read_idx;

    vector<int> seen_stamp;
    int stamp;
    int strategy_id;
    bool can_publish;
    vector<uint8_t> min_state; // 0=unvisited, 1=in_learned, 2=removable, 3=failed
    vector<int> min_stack;
    const vector<int>* carry_vars_ptr;
    vector<int> all_msg_vars;
    int cube_leaves_count = 0;
    int cube_min_msg_assigned = 100000;
    int cube_max_msg_assigned = 0;
    long long cube_sum_msg_assigned = 0;
    atomic<uint64_t>* live_conflicts_ptr = nullptr;
    atomic<uint64_t>* live_decisions_ptr = nullptr;

    inline void set_live_telemetry(atomic<uint64_t>* c, atomic<uint64_t>* d) {
        live_conflicts_ptr = c;
        live_decisions_ptr = d;
    }

    VerifiedCDCL(int n, const vector<vector<int>>& initial_clauses, int s, int r_base, 
                 ClauseSharingPool* pool, int s_id = 0,
                 const vector<vector<int>>& msg_words = {},
                 const vector<vector<int>>& round_states = {},
                 const vector<int>* carries = nullptr,
                 bool publish_enabled = true)
        : num_vars(n), offset(n + 5), assigns(n + 1, -1), var_level(n + 1, -1),
          var_reason(n + 1, -1), saved_phase(n + 1, 0), prop_head(0), activity(n + 1, 0.0),
          var_inc(1.0), var_decay(0.95), order_heap(activity), conflicts(0), decisions(0),
          propagations(0), seed(s), rng(s), restart_base((uint64_t)r_base), luby_u(1), luby_v(1),
          shared_pool(pool), shared_read_idx(0), seen_stamp(n + 1, 0), stamp(0), strategy_id(s_id), can_publish(publish_enabled),
          min_state(n + 1, 0), carry_vars_ptr(carries) {
        
        watches.resize(2 * offset + 5);
        bin_watches.resize(2 * offset + 5);
        for (const auto& raw_c : initial_clauses) {
            vector<int> clean_c = raw_c;
            sort(clean_c.begin(), clean_c.end());
            clean_c.erase(unique(clean_c.begin(), clean_c.end()), clean_c.end());
            
            bool tautology = false;
            for (int lit : clean_c) {
                if (binary_search(clean_c.begin(), clean_c.end(), -lit)) {
                    tautology = true;
                    break;
                }
            }
            if (tautology) continue;

            if (clean_c.empty()) {
                root_unsat = true;
                continue;
            }

            int c_idx = (int)clauses.size();
            clauses.emplace_back(clean_c, false, 0);

            if (clean_c.size() >= 2) {
                watches[get_watch_idx(clean_c[0])].push_back({c_idx, clean_c[1]});
                watches[get_watch_idx(clean_c[1])].push_back({c_idx, clean_c[0]});
            } else if (clean_c.size() == 1) {
                watches[get_watch_idx(clean_c[0])].push_back({c_idx, clean_c[0]});
                if (!assign_literal(clean_c[0], 0, -1)) {
                    root_unsat = true;
                }
            }
        }

        // CRITICAL FIX: propagate all root units (VAR_TRUE, VAR_FALSE, equalities, cubes) at level 0
        if (!root_unsat && !trail.empty()) {
            if (propagate() != -1) {
                root_unsat = true;
            }
        }

        // VSIDS diversification vs VMTF-like aggressive decay
        if (strategy_id == 10 || strategy_id == 11) {
            var_decay = 0.82; // Aggressive decay (VMTF-like focus)
        } else if (strategy_id == 6) {
            var_decay = 0.88; // Deep descent 2
        } else if (strategy_id == 7) {
            var_decay = 0.92; // Deep descent 3
        } else if (strategy_id == 8) {
            var_decay = 0.85; // Fast Luby
        } else if (strategy_id == 9) {
            var_decay = 0.91; // Medium Luby
        } else if (strategy_id % 2 == 1) {
            var_decay = 0.90;
        } else {
            var_decay = 0.95;
        }

        // Random balanced phase for uniform distribution of addition carries
        uniform_real_distribution<double> dist(0.0, 1.0);
        for (int v = 1; v <= num_vars; ++v) {
            activity[v] = dist(rng) * 0.1;
            saved_phase[v] = (strategy_id % 2 == 1) ? ((rng() % 2 == 0) ? 1 : 0) : 0; // Phase 0 to search for a preimage with minimal carries
        }

        // 3. Zero-Carry Phase Bias (carry monotonicity):
        // All addition carry variables are forcibly initialized to phase 0.
        // Monotone carries in Maj dampen cascades and steer CDCL toward smooth solutions.
        if (carry_vars_ptr) {
            for (int cv : *carry_vars_ptr) {
                if (cv >= 1 && cv <= num_vars) {
                    saved_phase[cv] = 0;
                }
            }
        }

        // Absorber Hierarchy:
        // Message-schedule driver words get the highest priority,
        // while free absorber words (W5..W8, W13) stay at low priority,
        // so CDCL does not decide on them blindly but computes them via BCP.
        if (!msg_words.empty()) {
            for (size_t i = 0; i < msg_words.size(); ++i) {
                for (int v : msg_words[i]) all_msg_vars.push_back(v);
                double bonus = 1e2;
                if (i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 14 || i == 15) {
                    bonus = 5e5 + (16 - i) * 1e4; // Primary schedule drivers (224 bits)
                }
                // W9..W12, W5..W8, W13 remain free shock absorbers (288 bits of freedom)
                for (int v : msg_words[i]) activity[v] += bonus;
            }
        }

        order_heap.init(num_vars);
    }

    inline int get_watch_idx(int lit) const {
        return lit + offset;
    }

    inline int8_t value_of_lit(int lit) const {
        int v = abs(lit);
        int8_t val = assigns[v];
        if (val == -1) return -1;
        return (lit > 0) ? val : (1 - val);
    }

    inline bool assign_literal(int lit, int level, int reason_idx) {
        int v = abs(lit);
        int8_t cur = assigns[v];
        if (cur != -1) {
            int8_t needed = (lit > 0) ? 1 : 0;
            return (cur == needed);
        }
        assigns[v] = (lit > 0) ? 1 : 0;
        var_level[v] = level;
        var_reason[v] = reason_idx;
        saved_phase[v] = assigns[v];
        trail.push_back(lit);
        return true;
    }

    inline void bump_var(int v) {
        activity[v] += var_inc;
        order_heap.update(v);
        if (activity[v] > 1e100) {
            for (int i = 1; i <= num_vars; ++i) activity[i] *= 1e-100;
            var_inc *= 1e-100;
        }
    }

    inline void decay_activities() {
        var_inc *= (1.0 / var_decay);
    }

    int propagate() {
        while (prop_head < (int)trail.size()) {
            int lit = trail[prop_head++];
            propagations++;
            int false_lit = -lit;
            int w_idx = get_watch_idx(false_lit);

            auto& ws = watches[w_idx];
            size_t i = 0, j = 0;
            while (i < ws.size()) {
                auto w = ws[i];
                if (clauses[w.c_idx].deleted) {
                    i++;
                    continue;
                }
                if (value_of_lit(w.blocker) == 1) {
                    ws[j++] = w;
                    i++;
                    continue;
                }

                auto& c = clauses[w.c_idx];
                if (c.lits.size() == 1) {
                    ws[j++] = w;
                    i++;
                    if (value_of_lit(c.lits[0]) == 0) return w.c_idx; // Unit conflict
                    continue;
                }

                if (c.lits[c.w1] == false_lit) swap(c.w1, c.w2);

                int first_lit = c.lits[c.w1];
                w.blocker = first_lit;
                if (value_of_lit(first_lit) == 1) {
                    ws[j++] = w;
                    i++;
                    continue;
                }

                bool found_new_watch = false;
                for (int k = 0; k < (int)c.lits.size(); ++k) {
                    if (k != c.w1 && k != c.w2 && value_of_lit(c.lits[k]) != 0) {
                        c.w2 = k;
                        watches[get_watch_idx(c.lits[k])].push_back(w);
                        found_new_watch = true;
                        break;
                    }
                }

                if (found_new_watch) {
                    i++;
                } else {
                    ws[j++] = w;
                    i++;
                    if (value_of_lit(first_lit) == 0) {
                        while (i < ws.size()) ws[j++] = ws[i++];
                        ws.resize(j);
                        return w.c_idx; // Clause conflict!
                    } else {
                        assign_literal(first_lit, (int)trail_lim.size(), w.c_idx);
                    }
                }
            }
            ws.resize(j);
        }
        return -1; // No conflict
    }

    // Canonical recursive minimization of learned clauses (MiniSat / Marques-Silva algorithm)
    bool is_redundant_rec(int p, uint32_t abstract_levels, int depth = 0) {
        if (depth > 256) return false;
        int v = abs(p);
        if (min_state[v] == 2) return true; // proven redundant
        if (min_state[v] == 3) return false; // proven irredundant

        int r = var_reason[v];
        if (r == -1 || clauses[r].deleted) {
            min_state[v] = 3;
            min_stack.push_back(v);
            return false;
        }

        // Abstract-level filter: if a variable's level is absent from the learned clause, it cannot be reduced
        if (((1U << (var_level[v] & 31)) & abstract_levels) == 0) {
            min_state[v] = 3;
            min_stack.push_back(v);
            return false;
        }

        const auto& r_lits = clauses[r].lits;
        for (int q : r_lits) {
            int qv = abs(q);
            if (qv == v) continue;
            if (var_level[qv] == 0) continue; // level 0 is an unconditional fact
            if (min_state[qv] == 1 || min_state[qv] == 2) continue; // already in learned or proven redundant
            if (!is_redundant_rec(qv, abstract_levels, depth + 1)) {
                min_state[v] = 3;
                min_stack.push_back(v);
                return false;
            }
        }

        min_state[v] = 2;
        min_stack.push_back(v);
        return true;
    }

    bool lit_redundant_canonical(int lit, uint32_t abstract_levels) {
        int v = abs(lit);
        int r = var_reason[v];
        if (r == -1) return false;

        const auto& r_lits = clauses[r].lits;
        for (int q : r_lits) {
            int qv = abs(q);
            if (qv == v) continue;
            if (var_level[qv] == 0) continue;
            if (min_state[qv] == 1 || min_state[qv] == 2) continue;
            if (!is_redundant_rec(qv, abstract_levels, 1)) return false;
        }
        return true;
    }

    void analyze_conflict(int conflict_c_idx, vector<int>& learned, int& backtrack_level, int& lbd) {
        // diagnostic disabled
        int current_level = (int)trail_lim.size();
        learned.clear();
        stamp++;
        if (stamp >= 0x7FFFFFFF) {
            fill(seen_stamp.begin(), seen_stamp.end(), 0);
            stamp = 1;
        }
        int counter = 0;
        int p_lit = 0;

        vector<int> curr_lits = clauses[conflict_c_idx].lits;
        int trail_idx = (int)trail.size() - 1;

        while (true) {
            for (int lit : curr_lits) {
                int var = abs(lit);
                if (seen_stamp[var] != stamp) {
                    seen_stamp[var] = stamp;
                    bump_var(var);
                    if (var_level[var] == current_level) {
                        counter++;
                    } else if (var_level[var] > 0) {
                        learned.push_back(lit);
                    }
                }
            }

            while (trail_idx >= 0) {
                p_lit = trail[trail_idx--];
                int var = abs(p_lit);
                if (seen_stamp[var] == stamp && var_level[var] == current_level) break;
            }

            counter--;
            if (counter == 0) {
                int uip_lit = -p_lit;
                learned.push_back(uip_lit);
                break;
            }

            int reason_idx = var_reason[abs(p_lit)];
            curr_lits = (reason_idx != -1) ? clauses[reason_idx].lits : vector<int>();
        }

        int uip_lit = learned.back();
        if (learned.size() > 2) {
            uint32_t abstract_levels = 0;
            for (int lit : learned) {
                abstract_levels |= (1U << (var_level[abs(lit)] & 31));
                min_state[abs(lit)] = 1;
                min_stack.push_back(abs(lit));
            }

            vector<int> clean_learned;
            for (size_t k = 0; k < learned.size() - 1; ++k) {
                int lit = learned[k];
                if (!lit_redundant_canonical(lit, abstract_levels)) {
                    clean_learned.push_back(lit);
                }
            }
            clean_learned.push_back(uip_lit);
            learned = move(clean_learned);

            for (int v : min_stack) min_state[v] = 0;
            min_stack.clear();
        }

        backtrack_level = 0;
        vector<int> levels;
        for (int lit : learned) {
            int var = abs(lit);
            if (lit != uip_lit) backtrack_level = max(backtrack_level, var_level[var]);
            if (var_level[var] > 0) levels.push_back(var_level[var]);
        }
        sort(levels.begin(), levels.end());
        levels.erase(unique(levels.begin(), levels.end()), levels.end());
        lbd = max(1, (int)levels.size());
    }

    void seed_phases(const vector<int8_t>& init_phases) {
        for (int v = 1; v <= num_vars && v < (int)init_phases.size(); ++v) {
            if (init_phases[v] != -1) {
                saved_phase[v] = init_phases[v];
            }
        }
    }

    void backtrack(int level) {
        if ((int)trail_lim.size() <= level) return;
        int target_len = trail_lim[level];
        while ((int)trail.size() > target_len) {
            int lit = trail.back();
            trail.pop_back();
            int v = abs(lit);
            assigns[v] = -1;
            var_level[v] = -1;
            var_reason[v] = -1;
            order_heap.insert(v);
        }
        trail_lim.resize(level);
        prop_head = target_len;
    }

    void reduce_clause_db() {
        vector<pair<int, int>> learned_indices;
        for (int i = 0; i < (int)clauses.size(); ++i) {
            if (!clauses[i].deleted && clauses[i].learned && clauses[i].lits.size() > 2) {
                learned_indices.push_back({clauses[i].lbd, i});
            }
        }
        if (learned_indices.empty()) return;

        sort(learned_indices.begin(), learned_indices.end());
        int keep_count = (int)learned_indices.size() / 2;

        for (size_t i = keep_count; i < learned_indices.size(); ++i) {
            int c_idx = learned_indices[i].second;
            if (clauses[c_idx].lbd > 2) {
                bool is_reason = false;
                for (int lit : clauses[c_idx].lits) {
                    if (var_reason[abs(lit)] == c_idx) {
                        is_reason = true;
                        break;
                    }
                }
                if (!is_reason) {
                    clauses[c_idx].deleted = true;
                    vector<int>().swap(clauses[c_idx].lits);
                }
            }
        }
    }

    bool import_shared_clauses_at_root() {
        if (!shared_pool) return true;
        vector<SharedClause> new_clauses;
        shared_pool->fetch(shared_read_idx, new_clauses, strategy_id);
        for (const auto& sc : new_clauses) {
            if (sc.lits.empty()) continue;

            // 1. Deduplication: skip clauses already satisfied at the root level
            bool already_sat = false;
            for (int lit : sc.lits) {
                if (value_of_lit(lit) == 1) {
                    already_sat = true;
                    break;
                }
            }
            if (already_sat) continue;

            // 2. Unary lemmas (units): assign immediately without bloating the clause database
            if (sc.lits.size() == 1) {
                int lit = sc.lits[0];
                int val = value_of_lit(lit);
                if (val == 0) return false; // Root conflict
                if (val == -1) {
                    if (!assign_literal(lit, 0, -1)) return false;
                }
                continue;
            }

            // 3. Add the clause to the database and register its 2WL watches
            int c_idx = (int)clauses.size();
            clauses.emplace_back(sc.lits, true, sc.lbd);
            auto& c = clauses.back();
            int w1 = -1, w2 = -1;
            for (int k = 0; k < (int)c.lits.size(); ++k) {
                if (value_of_lit(c.lits[k]) != 0) {
                    if (w1 == -1) w1 = k;
                    else { w2 = k; break; }
                }
            }
            if (w1 == -1) {
                return false; // Root conflict: all literals are false at level 0
            } else if (w2 == -1) {
                c.w1 = w1; c.w2 = w1;
                watches[get_watch_idx(c.lits[w1])].push_back({c_idx, c.lits[w1]});
                if (value_of_lit(c.lits[w1]) == -1) {
                    if (!assign_literal(c.lits[w1], 0, c_idx)) return false;
                } else if (value_of_lit(c.lits[w1]) == 0) {
                    return false;
                }
            } else {
                c.w1 = w1; c.w2 = w2;
                watches[get_watch_idx(c.lits[w1])].push_back({c_idx, c.lits[w2]});
                watches[get_watch_idx(c.lits[w2])].push_back({c_idx, c.lits[w1]});
            }
        }
        return (propagate() == -1);
    }

    int solve(double timeout_sec, atomic<bool>& stop_flag, uint64_t conflict_cutoff = 0) {
        if (root_unsat) return 0; // Instant pruning of inconsistent cubes
        auto start = chrono::high_resolution_clock::now();
        if (propagate() != -1) return 0; // UNSAT

        uint64_t next_restart = (restart_base > 0) ? (uint64_t)restart_base : UINT64_MAX;
        uint64_t next_reduce = 2000;
        uint64_t next_import = 2000;
        luby_u = 1;
        luby_v = 1;

        while (!stop_flag.load(memory_order_relaxed)) {
            if ((conflicts & 1023) == 0) {
                auto now = chrono::high_resolution_clock::now();
                if (chrono::duration<double>(now - start).count() > timeout_sec) return -1;
            }
            if (conflict_cutoff > 0 && conflicts >= conflict_cutoff) return -1;

            int conflict_c_idx = propagate();
            if (conflict_c_idx != -1) {
                conflicts++;
                if (live_conflicts_ptr && (conflicts & 1023) == 0) live_conflicts_ptr->fetch_add(1024);

                if (trail_lim.empty()) {
                    if (live_conflicts_ptr) live_conflicts_ptr->fetch_add(conflicts & 1023);
                    if (live_decisions_ptr) live_decisions_ptr->fetch_add(decisions & 2047);
                    return 0;
                }

                vector<int> learned;
                int backjump_level = 0;
                int lbd = 0;
                analyze_conflict(conflict_c_idx, learned, backjump_level, lbd);
                decay_activities();

                backtrack(backjump_level);

                int c_idx = (int)clauses.size();
                clauses.emplace_back(learned, true, lbd);

                if (shared_pool && can_publish && (learned.size() <= 3 || lbd <= 2)) {
                    shared_pool->publish(learned, lbd, strategy_id);
                }

                if (learned.size() >= 2) {
                    int uip_lit = learned.back();
                    int other_idx = 0;
                    int max_lvl = -1;
                    for (int k = 0; k < (int)learned.size() - 1; ++k) {
                        int lvl = var_level[abs(learned[k])];
                        if (lvl > max_lvl) {
                            max_lvl = lvl;
                            other_idx = k;
                        }
                    }
                    clauses[c_idx].w1 = (int)learned.size() - 1;
                    clauses[c_idx].w2 = other_idx;
                    int other_lit = learned[other_idx];
                    watches[get_watch_idx(uip_lit)].push_back({c_idx, other_lit});
                    watches[get_watch_idx(other_lit)].push_back({c_idx, uip_lit});
                    assign_literal(uip_lit, backjump_level, c_idx);
                } else if (learned.size() == 1) {
                    clauses[c_idx].w1 = 0;
                    watches[get_watch_idx(learned[0])].push_back({c_idx, learned[0]});
                    assign_literal(learned[0], 0, c_idx);
                }

                if (conflicts >= (uint64_t)next_reduce) {
                    reduce_clause_db();
                    next_reduce = conflicts + 2000;
                }

                if (restart_base > 0 && conflicts >= next_restart) {
                    backtrack(0);
                    if (!import_shared_clauses_at_root()) return 0;
                    uint64_t luby_val = luby_v;
                    if ((luby_u & -luby_u) == luby_v) {
                        luby_u++;
                        luby_v = 1;
                    } else {
                        luby_v++;
                    }
                    next_restart = conflicts + (uint64_t)restart_base * luby_val;
                }
                continue;
            }

            int var = -1;
            while (!order_heap.empty()) {
                int cand = order_heap.pop_max();
                if (assigns[cand] == -1) {
                    var = cand;
                    break;
                }
            }

            if (var == -1) {
                if (live_conflicts_ptr) live_conflicts_ptr->fetch_add(conflicts & 1023);
                if (live_decisions_ptr) live_decisions_ptr->fetch_add(decisions & 2047);
                return 1; // SAT!
            }

            decisions++;
            if (live_decisions_ptr && (decisions & 2047) == 0) live_decisions_ptr->fetch_add(2048);
            trail_lim.push_back((int)trail.size());
            int sign = (saved_phase[var] == 1) ? var : -var;
            assign_literal(sign, (int)trail_lim.size(), -1);
        }
        if (live_conflicts_ptr) live_conflicts_ptr->fetch_add(conflicts & 1023);
        if (live_decisions_ptr) live_decisions_ptr->fetch_add(decisions & 2047);
        return -1;
    }

    int probe_literals(const vector<int>& candidate_vars, vector<int>& found_units) {
        if (propagate() != -1) return -1;
        int count = 0;
        for (int v : candidate_vars) {
            if (v <= 0 || v > num_vars || assigns[v] != -1) continue;

            // 1. Try +v at level 1
            trail_lim.push_back((int)trail.size());
            assign_literal(v, 1, -1);
            int conflict = propagate();
            backtrack(0);

            if (conflict != -1) {
                assign_literal(-v, 0, -1);
                found_units.push_back(-v);
                count++;
                if (propagate() != -1) return -1;
                continue;
            }

            // 2. Try -v at level 1
            trail_lim.push_back((int)trail.size());
            assign_literal(-v, 1, -1);
            conflict = propagate();
            backtrack(0);

            if (conflict != -1) {
                assign_literal(v, 0, -1);
                found_units.push_back(v);
                count++;
                if (propagate() != -1) return -1;
            }
        }
        return count;
    }

    // -------------------------------------------------------------
    // LOOKAHEAD VARIABLE SCORING (BCP PROPAGATION SCORE)
    // March / Cube-and-Conquer metric: (P+ + 1) * (P- + 1) + 1024 * (P+ * P-)
    // -------------------------------------------------------------
    void score_lookahead_candidates(const vector<int>& candidates, vector<pair<double, int>>& scored_vars) {
        if (propagate() != -1) return;
        scored_vars.clear();

        for (int v : candidates) {
            if (v <= 0 || v > num_vars || assigns[v] != -1) continue;

            // 1. Positive branch +v
            trail_lim.push_back((int)trail.size());
            assign_literal(v, (int)trail_lim.size(), -1);
            int conf_pos = propagate();
            int prop_pos = (conf_pos != -1) ? -1 : ((int)trail.size() - trail_lim.back());
            backtrack(0);

            // 2. Negative branch -v
            trail_lim.push_back((int)trail.size());
            assign_literal(-v, (int)trail_lim.size(), -1);
            int conf_neg = propagate();
            int prop_neg = (conf_neg != -1) ? -1 : ((int)trail.size() - trail_lim.back());
            backtrack(0);

            // Handle root units when either branch yields a conflict
            if (conf_pos != -1 && conf_neg != -1) {
                root_unsat = true;
                return;
            } else if (conf_pos != -1) {
                assign_literal(-v, 0, -1);
                if (propagate() != -1) { root_unsat = true; return; }
                continue;
            } else if (conf_neg != -1) {
                assign_literal(v, 0, -1);
                if (propagate() != -1) { root_unsat = true; return; }
                continue;
            }

            double s = (double)(prop_pos + 1) * (double)(prop_neg + 1) + 1024.0 * (double)(prop_pos * prop_neg);
            scored_vars.push_back({s, v});
        }

        sort(scored_vars.rbegin(), scored_vars.rend());
    }

    // Recursive construction of a consistent cube tree with BCP pruning of branches
    void build_lookahead_cube_tree(const vector<int>& chosen_vars, int idx, int max_depth,
                                   vector<int>& current_cube, vector<vector<int>>& out_cubes) {
        if (root_unsat) return;
        if (idx >= (int)chosen_vars.size() || (int)current_cube.size() >= max_depth) {
            if (!current_cube.empty()) {
                out_cubes.push_back(current_cube);
                if (!all_msg_vars.empty()) {
                    int assigned_msg = 0;
                    for (int v : all_msg_vars) {
                        if (assigns[v] != -1) assigned_msg++;
                    }
                    cube_leaves_count++;
                    cube_sum_msg_assigned += assigned_msg;
                    if (assigned_msg < cube_min_msg_assigned) cube_min_msg_assigned = assigned_msg;
                    if (assigned_msg > cube_max_msg_assigned) cube_max_msg_assigned = assigned_msg;
                }
            }
            return;
        }

        int var = chosen_vars[idx];
        if (assigns[var] != -1) {
            build_lookahead_cube_tree(chosen_vars, idx + 1, max_depth, current_cube, out_cubes);
            return;
        }

        int base_lvl = (int)trail_lim.size();

        // Branch +var
        trail_lim.push_back((int)trail.size());
        assign_literal(var, (int)trail_lim.size(), -1);
        int c_pos = propagate();
        if (c_pos == -1) {
            current_cube.push_back(var);
            build_lookahead_cube_tree(chosen_vars, idx + 1, max_depth, current_cube, out_cubes);
            current_cube.pop_back();
        }
        backtrack(base_lvl);

        // Branch -var
        trail_lim.push_back((int)trail.size());
        assign_literal(-var, (int)trail_lim.size(), -1);
        int c_neg = propagate();
        if (c_neg == -1) {
            current_cube.push_back(-var);
            build_lookahead_cube_tree(chosen_vars, idx + 1, max_depth, current_cube, out_cubes);
            current_cube.pop_back();
        }
        backtrack(base_lvl);
    }
};

// =====================================================================
// BIT MATRIX FOR GAUSS-JORDAN ELIMINATION OVER F_2
// =====================================================================
class GF2BitMatrix {
public:
    int num_vars;
    int words_per_row;
    vector<vector<uint64_t>> rows;

    GF2BitMatrix(int n_vars) : num_vars(n_vars) {
        words_per_row = (num_vars + 64) / 64;
    }

    void add_equation(const vector<int>& vars, int rhs) {
        vector<uint64_t> row(words_per_row, 0);
        for (int v : vars) {
            if (v <= 0 || v > num_vars) continue;
            int w = v / 64;
            int b = v % 64;
            row[w] ^= (1ULL << b);
        }
        if (rhs & 1) row[0] ^= 1ULL;
        rows.push_back(move(row));
    }

    bool eliminate(vector<pair<int, int>>& implied_units,
                   vector<tuple<int, int, int>>& implied_binaries,
                   vector<tuple<int, int, int, int>>& implied_ternaries,
                   vector<tuple<int, int, int, int, int>>& implied_quaternaries) {
        int num_rows = (int)rows.size();
        int r = 0;

        for (int col = 1; col <= num_vars && r < num_rows; ++col) {
            int word_idx = col / 64;
            uint64_t bit_mask = (1ULL << (col % 64));

            int pivot = -1;
            for (int i = r; i < num_rows; ++i) {
                if (rows[i][word_idx] & bit_mask) {
                    pivot = i;
                    break;
                }
            }
            if (pivot == -1) continue;

            swap(rows[r], rows[pivot]);

            // Forward and backward Gauss-Jordan elimination
            for (int i = 0; i < num_rows; ++i) {
                if (i != r && (rows[i][word_idx] & bit_mask)) {
                    for (int w = 0; w < words_per_row; ++w) {
                        rows[i][w] ^= rows[r][w];
                    }
                }
            }
            r++;
        }

        // Extract linear consequences
        for (int i = 0; i < num_rows; ++i) {
            int count_vars = 0;
            int v1 = -1, v2 = -1, v3 = -1, v4 = -1;

            for (int col = 1; col <= num_vars; ++col) {
                int w = col / 64;
                uint64_t m = (1ULL << (col % 64));
                if (rows[i][w] & m) {
                    count_vars++;
                    if (count_vars == 1) v1 = col;
                    else if (count_vars == 2) v2 = col;
                    else if (count_vars == 3) v3 = col;
                    else if (count_vars == 4) v4 = col;
                }
            }

            int rhs = (rows[i][0] & 1ULL) ? 1 : 0;
            if (count_vars == 0 && rhs == 1) {
                return false; // Linear contradiction 0 = 1! UNSAT
            } else if (count_vars == 1) {
                implied_units.push_back({v1, rhs});
            } else if (count_vars == 2) {
                implied_binaries.push_back({v1, v2, rhs});
            } else if (count_vars == 3) {
                implied_ternaries.push_back({v1, v2, v3, rhs});
            } else if (count_vars == 4) {
                implied_quaternaries.push_back({v1, v2, v3, v4, rhs});
            }
        }
        return true;
    }

    vector<int8_t> extract_sample_solution() {
        vector<int8_t> sol(num_vars + 1, 0);
        int num_rows = (int)rows.size();
        for (int i = num_rows - 1; i >= 0; --i) {
            int pivot_col = -1;
            for (int col = 1; col <= num_vars; ++col) {
                int w = col / 64;
                uint64_t m = (1ULL << (col % 64));
                if (rows[i][w] & m) {
                    pivot_col = col;
                    break;
                }
            }
            if (pivot_col == -1) continue;
            int rhs = (rows[i][0] & 1ULL) ? 1 : 0;
            int p = rhs;
            for (int col = pivot_col + 1; col <= num_vars; ++col) {
                int w = col / 64;
                uint64_t m = (1ULL << (col % 64));
                if (rows[i][w] & m) {
                    p ^= sol[col];
                }
            }
            sol[pivot_col] = p;
        }
        return sol;
    }
};

// =====================================================================
// SHA-256 CIRCUIT BUILDER (ADDERS, SIGMA, CH, MAJ)
// =====================================================================
struct XorEq {
    vector<int> vars;
    int rhs;
};

class FastCircuitSHA256 {
public:
    int next_var;
    int VAR_TRUE;
    int VAR_FALSE;
    vector<vector<int>> clauses;
    vector<XorEq> xor_equations;
    bool record_carries = false;
    vector<int> recorded_carries;
    vector<int> all_carry_vars;

    FastCircuitSHA256() {
        next_var = 1;
        VAR_TRUE = alloc_var();
        VAR_FALSE = alloc_var();
        add_c({VAR_TRUE});
        add_c({-VAR_FALSE});
        add_xor_eq({VAR_TRUE}, 1);
        add_xor_eq({VAR_FALSE}, 0);
    }

    vector<int> const_word(uint32_t val, int bits = 32) {
        vector<int> res(bits);
        for (int b = 0; b < bits; ++b) {
            bool bit_val = (b < 32) ? ((val >> b) & 1) : 0;
            res[b] = bit_val ? VAR_TRUE : VAR_FALSE;
        }
        return res;
    }

    int alloc_var() {
        return next_var++;
    }

    vector<int> alloc_word(int bits = 32) {
        vector<int> w;
        for (int i = 0; i < bits; ++i) w.push_back(alloc_var());
        return w;
    }

    void add_c(const vector<int>& c) {
        clauses.push_back(c);
        if (c.size() == 1) {
            xor_equations.push_back({{abs(c[0])}, c[0] > 0 ? 1 : 0});
        }
    }

    void add_xor_eq(const vector<int>& lits, int rhs) {
        vector<int> abs_vars;
        for (int lit : lits) {
            if (lit < 0) {
                rhs ^= 1;
                abs_vars.push_back(-lit);
            } else if (lit > 0) {
                abs_vars.push_back(lit);
            }
        }
        xor_equations.push_back({abs_vars, rhs & 1});
    }

    int gate_xor(int a, int b) {
        int out = alloc_var();
        add_c({-a, -b, -out});
        add_c({a, b, -out});
        add_c({a, -b, out});
        add_c({-a, b, out});
        add_xor_eq({a, b, out}, 0);
        return out;
    }

    int gate_xor3(int a, int b, int c) {
        int out = alloc_var();
        // 8 parity clauses: forbid odd states (a ^ b ^ c ^ out == 1)
        for (int mask = 0; mask < 16; ++mask) {
            int p = (mask & 1) ^ ((mask >> 1) & 1) ^ ((mask >> 2) & 1) ^ ((mask >> 3) & 1);
            if (p == 1) {
                add_c({
                    (mask & 1) ? -a : a,
                    (mask & 2) ? -b : b,
                    (mask & 4) ? -c : c,
                    (mask & 8) ? -out : out
                });
            }
        }
        add_xor_eq({a, b, c, out}, 0);
        return out;
    }

    int gate_and(int a, int b) {
        int out = alloc_var();
        add_c({-out, a});
        add_c({-out, b});
        add_c({out, -a, -b});
        return out;
    }

    // Ch(E, F, G) = (E & F) ^ (~E & G) = Mux(E, F, G)
    int gate_ch(int e, int f, int g) {
        int out = alloc_var();
        add_c({-e, -f, out});
        add_c({-e, f, -out});
        add_c({e, -g, out});
        add_c({e, g, -out});
        return out;
    }

    // Maj(A, B, C) = (A & B) ^ (A & C) ^ (B & C)
    int gate_maj(int a, int b, int c) {
        int out = alloc_var();
        add_c({-a, -b, out});
        add_c({-a, -c, out});
        add_c({-b, -c, out});
        add_c({a, b, -out});
        add_c({a, c, -out});
        add_c({b, c, -out});
        return out;
    }

    pair<int, int> full_adder(int a, int b, int cin) {
        int g = alloc_var(); // Generate: g = a & b
        int p = alloc_var(); // Propagate: p = a ^ b
        int s = alloc_var(); // Sum: s = p ^ cin
        int cout = alloc_var(); // Cout: cout <-> g | (p & cin)

        // 1. g = a & b (3 clauses)
        add_c({-a, -b, g});
        add_c({a, -g});
        add_c({b, -g});

        // 2. p = a ^ b (4 clauses)
        add_c({-a, -b, -p});
        add_c({a, b, -p});
        add_c({a, -b, p});
        add_c({-a, b, p});
        add_xor_eq({a, b, p}, 0);

        // 3. s = p ^ cin (4 clauses)
        add_c({-p, -cin, -s});
        add_c({p, cin, -s});
        add_c({p, -cin, s});
        add_c({-p, cin, s});
        add_xor_eq({p, cin, s}, 0);

        // 4. cout <-> g | (p & cin) (4 clauses: 1 binary + 3 ternary)
        add_c({-g, cout});           // Binary clause: g=1 -> cout=1
        add_c({-p, -cin, cout});     // p=1 & cin=1 -> cout=1
        add_c({g, p, -cout});        // cout=1 -> g=1 or p=1
        add_c({g, cin, -cout});      // cout=1 -> g=1 or cin=1

        return {s, cout};
    }

    vector<int> word_add(const vector<int>& a, const vector<int>& b) {
        int w = (int)a.size();
        vector<int> res;
        int cin = 0;
        for (int i = 0; i < w; ++i) {
            if (i == 0) {
                int s = gate_xor(a[i], b[i]);
                int cout = gate_and(a[i], b[i]);
                cin = cout;
                res.push_back(s);
                all_carry_vars.push_back(cout);
                if (record_carries) recorded_carries.push_back(cout);
            } else {
                auto fa = full_adder(a[i], b[i], cin);
                cin = fa.second;
                res.push_back(fa.first);
                all_carry_vars.push_back(fa.second);
                if (record_carries) recorded_carries.push_back(fa.second);
            }
        }
        return res;
    }

    vector<int> word_add_const(const vector<int>& a, uint32_t c) {
        int w = (int)a.size();
        vector<int> b(w);
        for (int i = 0; i < w; ++i) {
            b[i] = ((c >> i) & 1) ? VAR_TRUE : VAR_FALSE;
        }
        return word_add(a, b);
    }

    // Modular subtraction (a - b mod 2^32) via two's complement: a + (~b) + 1
    vector<int> word_sub(const vector<int>& a, const vector<int>& b) {
        int w = (int)a.size();
        vector<int> res;
        int cin = VAR_TRUE;
        for (int i = 0; i < w; ++i) {
            auto fa = full_adder(a[i], -b[i], cin);
            cin = fa.second;
            res.push_back(fa.first);
            all_carry_vars.push_back(fa.second);
            if (record_carries) recorded_carries.push_back(fa.second);
        }
        return res;
    }

    vector<int> word_rotr(const vector<int>& word, int shift) {
        int w = (int)word.size();
        shift = shift % w;
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = word[(b + shift) % w];
        }
        return res;
    }

    vector<int> word_shr(const vector<int>& word, int shift) {
        int w = (int)word.size();
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            if (b + shift < w) {
                res[b] = word[b + shift];
            } else {
                res[b] = VAR_FALSE;
            }
        }
        return res;
    }

    // Sig0(A) = ROTR^2(A) ^ ROTR^13(A) ^ ROTR^22(A)
    vector<int> word_Sig0(const vector<int>& a) {
        int w = 32;
        vector<int> r2 = word_rotr(a, 2);
        vector<int> r13 = word_rotr(a, 13);
        vector<int> r22 = word_rotr(a, 22);
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_xor3(r2[b], r13[b], r22[b]);
        }
        return res;
    }

    // Sig1(E) = ROTR^6(E) ^ ROTR^11(E) ^ ROTR^25(E)
    vector<int> word_Sig1(const vector<int>& e) {
        int w = 32;
        vector<int> r6 = word_rotr(e, 6);
        vector<int> r11 = word_rotr(e, 11);
        vector<int> r25 = word_rotr(e, 25);
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_xor3(r6[b], r11[b], r25[b]);
        }
        return res;
    }

    // sig0(W) = ROTR^7(W) ^ ROTR^18(W) ^ SHR^3(W)
    vector<int> word_sig0(const vector<int>& x) {
        int w = 32;
        vector<int> r7 = word_rotr(x, 7);
        vector<int> r18 = word_rotr(x, 18);
        vector<int> s3 = word_shr(x, 3);
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_xor3(r7[b], r18[b], s3[b]);
        }
        return res;
    }

    // sig1(W) = ROTR^17(W) ^ ROTR^19(W) ^ SHR^10(W)
    vector<int> word_sig1(const vector<int>& x) {
        int w = 32;
        vector<int> r17 = word_rotr(x, 17);
        vector<int> r19 = word_rotr(x, 19);
        vector<int> s10 = word_shr(x, 10);
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_xor3(r17[b], r19[b], s10[b]);
        }
        return res;
    }

    vector<int> word_ch(const vector<int>& e, const vector<int>& f, const vector<int>& g) {
        int w = 32;
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_ch(e[b], f[b], g[b]);
        }
        return res;
    }

    vector<int> word_maj(const vector<int>& a, const vector<int>& b_word, const vector<int>& c) {
        int w = 32;
        vector<int> res(w);
        for (int b = 0; b < w; ++b) {
            res[b] = gate_maj(a[b], b_word[b], c[b]);
        }
        return res;
    }

    void constrain_word_eq(const vector<int>& w_vars, uint32_t val) {
        for (int b = 0; b < 32; ++b) {
            bool exp_bit = (val >> b) & 1;
            add_c({exp_bit ? w_vars[b] : -w_vars[b]});
            add_xor_eq({w_vars[b]}, exp_bit ? 1 : 0);
        }
    }
};

// =====================================================================
// PORTFOLIO RUN FOR SHA-256
// =====================================================================
struct PortfolioResult {
    int verdict;
    int winner_thread;
    vector<int8_t> solution;
    uint64_t conflicts;
    uint64_t decisions;
};

PortfolioResult run_portfolio_sha256(int num_vars, const vector<vector<int>>& clauses, int num_threads, double timeout_sec,
                                     const vector<vector<int>>& msg_words = {},
                                     const vector<vector<int>>& round_states = {},
                                     const vector<vector<int>>& W_vars = {},
                                     const vector<int>& schedule_carries = {},
                                     const vector<int>& all_carry_vars = {},
                                     const vector<int8_t>& affine_sol = {},
                                     const vector<int8_t>& relaxed_sol = {},
                                     const vector<int8_t>& cascade_sol = {}) {
    atomic<bool> stop_flag(false);
    atomic<int> winning_thread(-1);
    atomic<int> global_verdict(-1);
    vector<int8_t> solution(num_vars + 1, -1);
    uint64_t w_conflicts = 0, w_decisions = 0;
    mutex result_mtx;

    ClauseSharingPool shared_pool;

    // -------------------------------------------------------------
    // LOOKAHEAD CUBE-AND-CONQUER (MATHEMATICAL GENERATOR OF 10-12 BIT CUBES)
    // Ranking by March propagation score: (P+ + 1) * (P- + 1) + 1024 * (P+ * P-)
    // Conflicting branches are pruned directly in the generation tree (lookahead BCP pruning)
    // -------------------------------------------------------------
    vector<vector<int>> lookahead_cubes;
    auto t_cube_start = chrono::high_resolution_clock::now();

    vector<int> candidates;
    for (int i = 0; i < (int)msg_words.size(); ++i) {
        for (int b : msg_words[i]) candidates.push_back(b);
    }
    // Cubes branch strictly on message bits W0..W15 (a direct split of the 512-bit space)

    VerifiedCDCL lookahead_probe(num_vars, clauses, 42, 100, nullptr, 0, msg_words, round_states, &all_carry_vars);
    vector<pair<double, int>> scored_vars;
    lookahead_probe.score_lookahead_candidates(candidates, scored_vars);

    int target_depth = 11; // Depth 11 bits: not 8 bits of noise but deep branching
    vector<int> top_vars;
    for (size_t i = 0; i < min((size_t)14, scored_vars.size()); ++i) {
        top_vars.push_back(scored_vars[i].second);
    }

    vector<int> cur_c;
    lookahead_probe.build_lookahead_cube_tree(top_vars, 0, target_depth, cur_c, lookahead_cubes);
    auto t_cube_end = chrono::high_resolution_clock::now();
    double dt_cubes = chrono::duration<double>(t_cube_end - t_cube_start).count();

    cout << "  🎲 [Lookahead Cubes (" << fixed << setprecision(3) << dt_cubes << "s)]: Generated " 
         << lookahead_cubes.size() << " consistent cubes of depth " << target_depth 
         << " bits (with BCP pruning)." << endl;
    if (lookahead_probe.cube_leaves_count > 0) {
        double avg_msg = (double)lookahead_probe.cube_sum_msg_assigned / lookahead_probe.cube_leaves_count;
        cout << "  📊 [Cube Message Space Reduction (W0..W15)]: leaves=" << lookahead_probe.cube_leaves_count
             << " | assigned msg bits (direct + BCP): avg=" << fixed << setprecision(1) << avg_msg
             << ", min=" << lookahead_probe.cube_min_msg_assigned
             << ", max=" << lookahead_probe.cube_max_msg_assigned
             << " (out of 512 message bits)" << endl;
    }

    atomic<uint64_t> total_conflicts(0);
    atomic<uint64_t> total_decisions(0);
    auto global_start = chrono::high_resolution_clock::now();
    vector<thread> workers;

    for (int t = 0; t < num_threads; ++t) {
        workers.emplace_back([t, &clauses,
                              &total_conflicts, &total_decisions,
                              &stop_flag, &winning_thread, &global_verdict, &solution, 
                              &w_conflicts, &w_decisions, &result_mtx, &global_start,
                              num_vars, timeout_sec, &msg_words, &round_states, &shared_pool, 
                              &affine_sol, &relaxed_sol, &cascade_sol, &all_carry_vars]() {

            if (t == 0) {
                // Thread 0: Fast Luby (r_base = 25), standard Zero-Carry Phase Bias, seed = 1050
                VerifiedCDCL solver(num_vars, clauses, 1050, 25, &shared_pool, 0, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 1) {
                // Thread 1: Homotopy attractor (if relaxed_sol is available) or Luby (r_base = 35)
                VerifiedCDCL solver(num_vars, clauses, 2039, 35, &shared_pool, 1, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                if (!relaxed_sol.empty()) solver.seed_phases(relaxed_sol);
                else if (!cascade_sol.empty()) solver.seed_phases(cascade_sol);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 2) {
                // Thread 2: F_2 affine attractor (if affine_sol is available), Luby (r_base = 30)
                VerifiedCDCL solver(num_vars, clauses, 3049, 30, &shared_pool, 2, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                if (!affine_sol.empty()) solver.seed_phases(affine_sol);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 3) {
                // Thread 3: REFERENCE 18-ROUND CHAMPION (4.12 s!)
                // Deep descent without restarts (r_base = 0), seed = 3058, strategy_id = 3 (var_decay = 0.90, random init + Zero-Carry bias)
                // Fully immune to phase attractors; publishes and imports global lemmas
                VerifiedCDCL solver(num_vars, clauses, 3058, 0, &shared_pool, 3, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 4) {
                // Thread 4: Global Luby (r_base = 45), seed = 4067, strategy_id = 4
                VerifiedCDCL solver(num_vars, clauses, 4067, 45, &shared_pool, 4, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 5) {
                // Thread 5: Global Luby (r_base = 75), seed = 5079, strategy_id = 5
                VerifiedCDCL solver(num_vars, clauses, 5079, 75, &shared_pool, 5, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 6) {
                // Thread 6: Deep Descent #2 (r_base = 0, var_decay = 0.88, aggressive focus on fresh conflicts)
                VerifiedCDCL solver(num_vars, clauses, 6089, 0, &shared_pool, 6, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 7) {
                // Thread 7: Deep Descent #3 (r_base = 0, var_decay = 0.92, balanced deep descent)
                VerifiedCDCL solver(num_vars, clauses, 7097, 0, &shared_pool, 7, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 8) {
                // Thread 8: Fast Luby (r_base = 15, var_decay = 0.85, fast scanning of local subspaces)
                VerifiedCDCL solver(num_vars, clauses, 8101, 15, &shared_pool, 8, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else if (t == 9) {
                // Thread 9: Medium Luby (r_base = 55, var_decay = 0.91)
                VerifiedCDCL solver(num_vars, clauses, 9109, 55, &shared_pool, 9, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) { global_verdict.store(0); stop_flag.store(true); }
                }
            } else {
                // Threads 10..11: VMTF-like aggressive focus (var_decay = 0.82), r_base = 80, 120
                int r_base = 80 + (t - 10) * 40;
                VerifiedCDCL solver(num_vars, clauses, t * 1009 + 31, r_base, &shared_pool, t, msg_words, round_states, &all_carry_vars, true);
                solver.set_live_telemetry(&total_conflicts, &total_decisions);
                int res = solver.solve(timeout_sec, stop_flag, 0);
                if (res == 1) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        winning_thread.store(t); global_verdict.store(1);
                        solution = solver.assigns; w_conflicts = solver.conflicts; w_decisions = solver.decisions;
                        stop_flag.store(true);
                    }
                } else if (res == 0) {
                    lock_guard<mutex> lock(result_mtx);
                    if (global_verdict.load() == -1) {
                        global_verdict.store(0);
                        stop_flag.store(true);
                    }
                }
            }
        });
    }
    thread monitor([&stop_flag, timeout_sec, &shared_pool, &total_conflicts, &total_decisions]() {
        auto m_start = chrono::high_resolution_clock::now();
        double last_report = 0.0;
        while (!stop_flag.load(memory_order_relaxed)) {
            this_thread::sleep_for(chrono::milliseconds(200));
            if (stop_flag.load(memory_order_relaxed)) break;
            double elapsed = chrono::duration<double>(chrono::high_resolution_clock::now() - m_start).count();
            if (elapsed >= timeout_sec) {
                stop_flag.store(true);
                break;
            }
            if (elapsed - last_report >= 30.0) {
                last_report = elapsed;
                cout << "  ⏱️ [" << (int)elapsed << "s / " << (int)timeout_sec << "s]: 12-thread assault (Continuous Swarm)" 
                     << " | Lemmas in ring: " << shared_pool.size() << "/" << ClauseSharingPool::CAPACITY 
                     << " (total: " << shared_pool.total() << ")"
                     << " | Conflicts: " << total_conflicts.load() 
                     << " | Decisions: " << total_decisions.load() << endl;
            }
        }
    });

    for (auto& w : workers) {
        if (w.joinable()) w.join();
    }
    stop_flag.store(true);
    if (monitor.joinable()) monitor.join();

    int winner = winning_thread.load();
    int verdict = global_verdict.load();
    return {verdict, winner, solution, w_conflicts, w_decisions};
}

// =====================================================================
// DIMACS CNF EXPORT FOR INDEPENDENT BENCHMARKING (Kissat / CryptoMiniSat)
// =====================================================================
void export_dimacs_cnf(const string& filename, int num_vars, const vector<vector<int>>& clauses) {
    ofstream out(filename);
    if (!out.is_open()) {
        cerr << "  ❌ Error creating file " << filename << endl;
        return;
    }
    out << "c SHA-256 Algebraic Inversion CNF (RFC 6234 / FIPS 180-4)\n";
    out << "p cnf " << num_vars << " " << clauses.size() << "\n";
    for (const auto& c : clauses) {
        for (int lit : c) out << lit << " ";
        out << "0\n";
    }
    out.close();
    cout << "  📁 [DIMACS CNF export]: saved file " << filename 
         << " (" << num_vars << " variables, " << clauses.size() << " clauses)" << endl;
}

// =====================================================================
// TEST HARNESS: BREAKING ROUND-REDUCED SHA-256 (RFC 6234)
// =====================================================================
void build_sha256_circuit(int rounds, const uint32_t target_digest[8],
                          FastCircuitSHA256& circuit,
                          vector<vector<int>>& msg_words,
                          vector<vector<int>>& W_vars,
                          vector<vector<int>>& round_states,
                          int spliced_registers = 8) {
    int w = 32;
    uint32_t target_state[8];
    for (int i = 0; i < 8; ++i) target_state[i] = target_digest[i] - IV_SHA256[i];

    msg_words.assign(16, vector<int>());
    for (int i = 0; i < 16; ++i) msg_words[i] = circuit.alloc_word(w);

    W_vars.assign(rounds, vector<int>());
    for (int i = 0; i < min(16, rounds); ++i) {
        W_vars[i] = msg_words[i];
    }
    circuit.record_carries = true;
    for (int i = 16; i < rounds; ++i) {
        auto s1 = circuit.word_sig1(W_vars[i - 2]);
        auto w7 = W_vars[i - 7];
        auto s0 = circuit.word_sig0(W_vars[i - 15]);
        auto w16 = W_vars[i - 16];
        auto sum1 = circuit.word_add(s1, w7);
        auto sum2 = circuit.word_add(sum1, s0);
        W_vars[i] = circuit.word_add(sum2, w16);
    }
    circuit.record_carries = false;

    vector<vector<int>> cur_state(8);
    for (int i = 0; i < 8; ++i) {
        cur_state[i].resize(w);
        for (int b = 0; b < w; ++b) {
            bool bit_val = (IV_SHA256[i] >> b) & 1;
            cur_state[i][b] = bit_val ? circuit.VAR_TRUE : circuit.VAR_FALSE;
        }
    }

    round_states.assign(rounds, vector<int>());

    uint32_t AR = target_state[0], BR = target_state[1], CR = target_state[2], DR = target_state[3];
    uint32_t ER = target_state[4], FR = target_state[5], GR = target_state[6], HR = target_state[7];

    if (rounds >= 19) {
        vector<vector<int>> cur_bwd(8);
        if (rounds == 19) {
            uint32_t reg_A_18 = BR, reg_B_18 = CR, reg_C_18 = DR;
            uint32_t reg_E_18 = FR, reg_F_18 = GR, reg_G_18 = HR;
            uint32_t T2_18 = Sig0(reg_A_18) + Maj(reg_A_18, reg_B_18, reg_C_18);
            uint32_t T1_18 = AR - T2_18;
            uint32_t reg_D_18 = ER - T1_18;
            uint32_t const_C_18 = T1_18 - Sig1(reg_E_18) - Ch(reg_E_18, reg_F_18, reg_G_18) - K_SHA256[18];
            auto H_18 = circuit.word_sub(circuit.const_word(const_C_18), W_vars[18]);

            uint32_t reg_A_17 = reg_B_18, reg_B_17 = reg_C_18, reg_C_17 = reg_D_18;
            uint32_t reg_E_17 = reg_F_18, reg_F_17 = reg_G_18;
            uint32_t T2_17 = Sig0(reg_A_17) + Maj(reg_A_17, reg_B_17, reg_C_17);
            uint32_t T1_17 = reg_A_18 - T2_17;
            uint32_t reg_D_17 = reg_E_18 - T1_17;
            uint32_t const_C_17 = T1_17 - Sig1(reg_E_17) - K_SHA256[17];

            vector<int> ch_17(w);
            for (int b = 0; b < w; ++b) {
                if ((reg_E_17 >> b) & 1) {
                    bool bit_val = (reg_F_17 >> b) & 1;
                    ch_17[b] = bit_val ? circuit.VAR_TRUE : circuit.VAR_FALSE;
                } else {
                    ch_17[b] = H_18[b];
                }
            }
            auto temp_17 = circuit.word_sub(circuit.const_word(const_C_17), W_vars[17]);
            auto H_17 = circuit.word_sub(temp_17, ch_17);

            uint32_t reg_A_16 = reg_B_17, reg_B_16 = reg_C_17, reg_C_16 = reg_D_17;
            uint32_t reg_E_16 = reg_F_17;
            uint32_t T2_16 = Sig0(reg_A_16) + Maj(reg_A_16, reg_B_16, reg_C_16);
            uint32_t T1_16 = reg_A_17 - T2_16;
            uint32_t reg_D_16 = reg_E_17 - T1_16;
            uint32_t const_C_16 = T1_16 - Sig1(reg_E_16) - K_SHA256[16];

            vector<int> ch_16(w);
            for (int b = 0; b < w; ++b) {
                if ((reg_E_16 >> b) & 1) {
                    ch_16[b] = H_18[b];
                } else {
                    ch_16[b] = H_17[b];
                }
            }
            auto temp_16 = circuit.word_sub(circuit.const_word(const_C_16), W_vars[16]);
            auto H_16 = circuit.word_sub(temp_16, ch_16);

            cur_bwd[0] = circuit.const_word(reg_A_16);
            cur_bwd[1] = circuit.const_word(reg_B_16);
            cur_bwd[2] = circuit.const_word(reg_C_16);
            cur_bwd[3] = circuit.const_word(reg_D_16);
            cur_bwd[4] = circuit.const_word(reg_E_16);
            cur_bwd[5] = H_18;
            cur_bwd[6] = H_17;
            cur_bwd[7] = H_16;
        } else {
            uint32_t reg_A_19 = BR, reg_B_19 = CR, reg_C_19 = DR;
            uint32_t reg_E_19 = FR, reg_F_19 = GR, reg_G_19 = HR;
            uint32_t T2_19 = Sig0(reg_A_19) + Maj(reg_A_19, reg_B_19, reg_C_19);
            uint32_t T1_19 = AR - T2_19;
            uint32_t reg_D_19 = ER - T1_19;
            uint32_t const_C_19 = T1_19 - Sig1(reg_E_19) - Ch(reg_E_19, reg_F_19, reg_G_19) - K_SHA256[19];

            uint32_t reg_A_18 = reg_B_19, reg_B_18 = reg_C_19, reg_C_18 = reg_D_19;
            uint32_t reg_E_18 = reg_F_19, reg_F_18 = reg_G_19;
            uint32_t T2_18 = Sig0(reg_A_18) + Maj(reg_A_18, reg_B_18, reg_C_18);
            uint32_t T1_18 = reg_A_19 - T2_18;
            uint32_t reg_D_18 = reg_E_19 - T1_18;
            uint32_t const_C_18 = T1_18 - Sig1(reg_E_18) - K_SHA256[18];

            uint32_t reg_A_17 = reg_B_18, reg_B_17 = reg_C_18, reg_C_17 = reg_D_18;
            uint32_t reg_E_17 = reg_F_18;
            uint32_t T2_17 = Sig0(reg_A_17) + Maj(reg_A_17, reg_B_17, reg_C_17);
            uint32_t T1_17 = reg_A_18 - T2_17;
            uint32_t reg_D_17 = reg_E_18 - T1_17;
            uint32_t const_C_17 = T1_17 - Sig1(reg_E_17) - K_SHA256[17];

            uint32_t reg_A_16 = reg_B_17, reg_B_16 = reg_C_17, reg_C_16 = reg_D_17;
            uint32_t T2_16 = Sig0(reg_A_16) + Maj(reg_A_16, reg_B_16, reg_C_16);
            uint32_t T1_16 = reg_A_17 - T2_16;
            uint32_t reg_D_16 = reg_E_17 - T1_16;
            uint32_t const_C_16 = T1_16 - K_SHA256[16];

            auto E_16 = circuit.word_sub(circuit.const_word(const_C_19), W_vars[19]);

            vector<int> ch_18(w);
            for (int b = 0; b < w; ++b) {
                if ((reg_E_18 >> b) & 1) {
                    bool bit_val = (reg_F_18 >> b) & 1;
                    ch_18[b] = bit_val ? circuit.VAR_TRUE : circuit.VAR_FALSE;
                } else {
                    ch_18[b] = E_16[b];
                }
            }
            auto temp_18 = circuit.word_sub(circuit.const_word(const_C_18), W_vars[18]);
            auto F_16 = circuit.word_sub(temp_18, ch_18);

            vector<int> ch_17(w);
            for (int b = 0; b < w; ++b) {
                if ((reg_E_17 >> b) & 1) {
                    ch_17[b] = E_16[b];
                } else {
                    ch_17[b] = F_16[b];
                }
            }
            auto temp_17 = circuit.word_sub(circuit.const_word(const_C_17), W_vars[17]);
            auto G_16 = circuit.word_sub(temp_17, ch_17);

            auto s1_E16 = circuit.word_Sig1(E_16);
            auto ch_16 = circuit.word_ch(E_16, F_16, G_16);
            auto temp_16a = circuit.word_sub(circuit.const_word(const_C_16), W_vars[16]);
            auto temp_16b = circuit.word_sub(temp_16a, s1_E16);
            auto H_16 = circuit.word_sub(temp_16b, ch_16);

            cur_bwd[0] = circuit.const_word(reg_A_16);
            cur_bwd[1] = circuit.const_word(reg_B_16);
            cur_bwd[2] = circuit.const_word(reg_C_16);
            cur_bwd[3] = circuit.const_word(reg_D_16);
            cur_bwd[4] = E_16;
            cur_bwd[5] = F_16;
            cur_bwd[6] = G_16;
            cur_bwd[7] = H_16;
        }

        vector<vector<int>> cur_fwd = cur_state;
        for (int r = 0; r < 8; ++r) {
            auto sA = cur_fwd[0], sB = cur_fwd[1], sC = cur_fwd[2], sD = cur_fwd[3];
            auto sE = cur_fwd[4], sF = cur_fwd[5], sG = cur_fwd[6], sH = cur_fwd[7];

            auto S1_E = circuit.word_Sig1(sE);
            auto ch_EFG = circuit.word_ch(sE, sF, sG);
            auto H_plus_S1 = circuit.word_add(sH, S1_E);
            auto T1_a = circuit.word_add(H_plus_S1, ch_EFG);
            auto T1_b = circuit.word_add_const(T1_a, K_SHA256[r]);
            auto T1 = circuit.word_add(T1_b, W_vars[r]);

            auto S0_A = circuit.word_Sig0(sA);
            auto maj_ABC = circuit.word_maj(sA, sB, sC);
            auto T2 = circuit.word_add(S0_A, maj_ABC);

            auto new_E = circuit.word_add(sD, T1);
            auto new_A = circuit.word_add(T1, T2);

            cur_fwd[7] = sG; cur_fwd[6] = sF; cur_fwd[5] = sE; cur_fwd[4] = new_E;
            cur_fwd[3] = sC; cur_fwd[2] = sB; cur_fwd[1] = sA; cur_fwd[0] = new_A;
            round_states[r] = new_A;
        }

        for (int r = 15; r >= 8; --r) {
            auto next_A = cur_bwd[0], next_B = cur_bwd[1], next_C = cur_bwd[2], next_D = cur_bwd[3];
            auto next_E = cur_bwd[4], next_F = cur_bwd[5], next_G = cur_bwd[6], next_H = cur_bwd[7];

            auto prev_A = next_B;
            auto prev_B = next_C;
            auto prev_C = next_D;
            auto prev_E = next_F;
            auto prev_F = next_G;
            auto prev_G = next_H;

            auto S0_A = circuit.word_Sig0(prev_A);
            auto maj_ABC = circuit.word_maj(prev_A, prev_B, prev_C);
            auto T2 = circuit.word_add(S0_A, maj_ABC);

            auto T1 = circuit.word_sub(next_A, T2);
            auto prev_D = circuit.word_sub(next_E, T1);

            auto S1_E = circuit.word_Sig1(prev_E);
            auto ch_EFG = circuit.word_ch(prev_E, prev_F, prev_G);
            auto term_a = circuit.word_add(S1_E, ch_EFG);
            auto term_b = circuit.word_add_const(term_a, K_SHA256[r]);
            auto term = circuit.word_add(term_b, W_vars[r]);
            auto prev_H = circuit.word_sub(T1, term);

            cur_bwd[0] = prev_A; cur_bwd[1] = prev_B; cur_bwd[2] = prev_C; cur_bwd[3] = prev_D;
            cur_bwd[4] = prev_E; cur_bwd[5] = prev_F; cur_bwd[6] = prev_G; cur_bwd[7] = prev_H;
            round_states[r] = prev_A;
        }

        // Honest homotopy: link spliced_registers out of 8 (from 4 to 8 registers)
        int num_splice_regs = max(1, min(8, spliced_registers));
        for (int reg = 0; reg < num_splice_regs; ++reg) {
            for (int b = 0; b < w; ++b) {
                int u = cur_fwd[reg][b];
                int v = cur_bwd[reg][b];
                circuit.add_c({-u, v});
                circuit.add_c({u, -v});
                circuit.add_xor_eq({u, v}, 0);
            }
        }
    } else {
        uint32_t A_1 = BR, B_1 = CR, C_1 = DR, E_1 = FR, F_1 = GR, G_1 = HR;
        uint32_t T2_1 = Sig0(A_1) + Maj(A_1, B_1, C_1);
        uint32_t T1_1 = AR - T2_1;
        uint32_t D_1 = ER - T1_1;
        uint32_t C_R_minus_1 = T1_1 - Sig1(E_1) - Ch(E_1, F_1, G_1) - K_SHA256[rounds - 1];

        uint32_t A_2 = CR, B_2 = DR, C_2 = D_1, E_2 = GR, F_2 = HR;
        uint32_t T2_2 = Sig0(A_2) + Maj(A_2, B_2, C_2);
        uint32_t T1_2 = A_1 - T2_2;
        uint32_t D_2 = E_1 - T1_2;
        uint32_t C_R_minus_2 = T1_2 - Sig1(E_2) - K_SHA256[rounds - 2];

        int forward_rounds = rounds - 2;
        for (int r = 0; r < forward_rounds; ++r) {
            auto sA = cur_state[0], sB = cur_state[1], sC = cur_state[2], sD = cur_state[3];
            auto sE = cur_state[4], sF = cur_state[5], sG = cur_state[6], sH = cur_state[7];

            auto S1_E = circuit.word_Sig1(sE);
            auto ch_EFG = circuit.word_ch(sE, sF, sG);
            auto H_plus_S1 = circuit.word_add(sH, S1_E);
            auto T1_a = circuit.word_add(H_plus_S1, ch_EFG);
            auto T1_b = circuit.word_add_const(T1_a, K_SHA256[r]);
            auto T1 = circuit.word_add(T1_b, W_vars[r]);

            auto S0_A = circuit.word_Sig0(sA);
            auto maj_ABC = circuit.word_maj(sA, sB, sC);
            auto T2 = circuit.word_add(S0_A, maj_ABC);

            auto new_E = circuit.word_add(sD, T1);
            auto new_A = circuit.word_add(T1, T2);

            cur_state[7] = sG; cur_state[6] = sF; cur_state[5] = sE; cur_state[4] = new_E;
            cur_state[3] = sC; cur_state[2] = sB; cur_state[1] = sA; cur_state[0] = new_A;
            round_states[r] = new_A;
        }

        circuit.constrain_word_eq(cur_state[0], A_2);
        circuit.constrain_word_eq(cur_state[1], B_2);
        circuit.constrain_word_eq(cur_state[2], C_2);
        circuit.constrain_word_eq(cur_state[3], D_2);
        circuit.constrain_word_eq(cur_state[4], E_2);
        circuit.constrain_word_eq(cur_state[5], F_2);

        auto G_R2 = cur_state[6];
        auto H_R2 = cur_state[7];

        vector<int> ch_R2(w);
        for (int b = 0; b < w; ++b) {
            if ((GR >> b) & 1) {
                bool bit_val = (HR >> b) & 1;
                ch_R2[b] = bit_val ? circuit.VAR_TRUE : circuit.VAR_FALSE;
            } else {
                ch_R2[b] = G_R2[b];
            }
        }

        auto sum_R2_a = circuit.word_add(W_vars[rounds - 2], H_R2);
        auto sum_R2 = circuit.word_add(sum_R2_a, ch_R2);
        circuit.constrain_word_eq(sum_R2, C_R_minus_2);

        auto sum_R1 = circuit.word_add(W_vars[rounds - 1], G_R2);
        circuit.constrain_word_eq(sum_R1, C_R_minus_1);
    }
}


// ---------------------------------------------------------------------------------
// HONEST SPLICE HOMOTOPY (TRUE MEET-IN-THE-MIDDLE CONSTRAINT HOMOTOPY)
// Input: ONLY the 256-bit target digest target_digest (black box).
// Zero secret data, zero intermediate hashes!
// ---------------------------------------------------------------------------------
vector<int8_t> run_pure_homotopy_ladder(int rounds, const uint32_t target_digest[8]) {
    vector<int8_t> current_seed;
    if (rounds < 19) return current_seed;

    int reached_regs = 0;

    // Step 1: 5 registers (160 bits of linked constraints)
    {
        auto t0 = chrono::high_resolution_clock::now();
        FastCircuitSHA256 c5;
        vector<vector<int>> mw5(16), wv5(rounds), rs5(rounds);
        build_sha256_circuit(rounds, target_digest, c5, mw5, wv5, rs5, 5);
        atomic<bool> stop5(false);
        VerifiedCDCL s5(c5.next_var - 1, c5.clauses, 101, 20, nullptr, 0, mw5, rs5, &c5.all_carry_vars);
        if (s5.solve(2.0, stop5, 15000) == 1) {
            current_seed = s5.assigns;
            reached_regs = 5;
            auto t1 = chrono::high_resolution_clock::now();
            cout << "  ⚡ [Honest homotopy 1/3]: 160-bit attractor found in " 
                 << fixed << setprecision(3) << chrono::duration<double>(t1 - t0).count() << "s!" << endl;
        }
    }

    // Step 2: 6 registers (192 bits of linked constraints) on 4 parallel cores
    {
        auto t0 = chrono::high_resolution_clock::now();
        FastCircuitSHA256 c6;
        vector<vector<int>> mw6(16), wv6(rounds), rs6(rounds);
        build_sha256_circuit(rounds, target_digest, c6, mw6, wv6, rs6, 6);
        atomic<bool> stop6(false);
        atomic<bool> solved6(false);
        vector<int8_t> sol6;
        mutex mtx6;
        vector<thread> pool6;
        for (int th = 0; th < 4; ++th) {
            pool6.emplace_back([th, &c6, &mw6, &rs6, &stop6, &solved6, &sol6, &mtx6, &current_seed]() {
                int r_base = (th == 0) ? 20 : ((th == 1) ? 35 : ((th == 2) ? 0 : 50));
                VerifiedCDCL s(c6.next_var - 1, c6.clauses, 103 + th * 37, r_base, nullptr, th, mw6, rs6, &c6.all_carry_vars);
                if (!current_seed.empty() && th <= 1) s.seed_phases(current_seed);
                if (s.solve(5.0, stop6, 50000) == 1) {
                    lock_guard<mutex> lock(mtx6);
                    if (!solved6.load()) {
                        solved6.store(true);
                        sol6 = s.assigns;
                        stop6.store(true);
                    }
                }
            });
        }
        for (auto& w : pool6) if (w.joinable()) w.join();
        if (solved6.load()) {
            current_seed = sol6;
            reached_regs = 6;
            auto t1 = chrono::high_resolution_clock::now();
            cout << "  ⚡ [Honest homotopy 2/3]: 192-bit attractor found in " 
                 << fixed << setprecision(3) << chrono::duration<double>(t1 - t0).count() << "s!" << endl;
        }
    }

    // Step 3: 7 registers (224 bits of linked constraints) on 4 parallel cores
    {
        auto t0 = chrono::high_resolution_clock::now();
        FastCircuitSHA256 c7;
        vector<vector<int>> mw7(16), wv7(rounds), rs7(rounds);
        build_sha256_circuit(rounds, target_digest, c7, mw7, wv7, rs7, 7);
        atomic<bool> stop7(false);
        atomic<bool> solved7(false);
        vector<int8_t> sol7;
        mutex mtx7;
        vector<thread> pool7;
        for (int th = 0; th < 4; ++th) {
            pool7.emplace_back([th, &c7, &mw7, &rs7, &stop7, &solved7, &sol7, &mtx7, &current_seed]() {
                int r_base = (th == 0) ? 25 : ((th == 1) ? 40 : ((th == 2) ? 0 : 65));
                VerifiedCDCL s(c7.next_var - 1, c7.clauses, 107 + th * 43, r_base, nullptr, th, mw7, rs7, &c7.all_carry_vars);
                if (!current_seed.empty() && th <= 1) s.seed_phases(current_seed);
                if (s.solve(8.0, stop7, 80000) == 1) {
                    lock_guard<mutex> lock(mtx7);
                    if (!solved7.load()) {
                        solved7.store(true);
                        sol7 = s.assigns;
                        stop7.store(true);
                    }
                }
            });
        }
        for (auto& w : pool7) if (w.joinable()) w.join();
        if (solved7.load()) {
            current_seed = sol7;
            reached_regs = 7;
            auto t1 = chrono::high_resolution_clock::now();
            cout << "  ⚡ [Honest homotopy 3/3]: 224-bit attractor found in " 
                 << fixed << setprecision(3) << chrono::duration<double>(t1 - t0).count() << "s!" << endl;
        }
    }

    if (reached_regs < 7) {
        if (reached_regs > 0) {
            cout << "  ⚠️ [Honest homotopy]: stage 3 did not converge before timeout (" 
                 << (reached_regs * 32) << "-bit attractor). To avoid false phase noise, the seed was discarded." << endl;
        } else {
            cout << "  ⚠️ [Honest homotopy]: no attractor found; search will start without phase bias." << endl;
        }
        return vector<int8_t>();
    }

    return current_seed;
}

void run_sha256_experiment(const vector<int>& target_rounds, bool cnf_only = false, double custom_timeout = 0.0, uint32_t target_seed = 0) {
    int hardware_threads = max(1u, (unsigned int)thread::hardware_concurrency());

    cout << "=================================================================" << endl;
    cout << "🟢 EXPERIMENT: ALGEBRAIC INVERSION OF SHA-256 (FIPS 180-4 / RFC 6234)" << endl;
    cout << "   256-bit state (A..H, 32 bits each). Message block: 512 bits" << endl;
    cout << "   Davis-Meyer feed-forward, round constants K[i]" << endl;
    cout << "   CPU threads: " << hardware_threads << endl;
    cout << "=================================================================" << endl;

    int w = 32;

    // Target 512-bit message block (16 words of 32 bits)
    uint32_t secret_M[16] = {
        0x61626380, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000018
    };

    if (target_seed != 0) {
        mt19937_64 gen(target_seed);
        for (int i = 0; i < 16; ++i) secret_M[i] = (uint32_t)gen();
        cout << "  🎲 [Random target message block (Seed: " << target_seed << ")]:" << endl;
        for (int i = 0; i < 16; ++i) {
            cout << "    M_target[" << setfill(' ') << setw(2) << i << "] = 0x" 
                 << hex << setfill('0') << setw(8) << secret_M[i] << dec << endl;
        }
    }

    for (int rounds : target_rounds) {
        cout << "\n-----------------------------------------------------------------" << endl;
        cout << "🎯 [SHA-256 RESEARCH | ROUNDS: " << rounds << "]:" << endl;

        // 1. Honest forward computation of reference SHA-256
        uint32_t W[64] = {0};
        for (int i = 0; i < 16; ++i) W[i] = secret_M[i];
        for (int i = 16; i < rounds; ++i) {
            W[i] = sig1(W[i - 2]) + W[i - 7] + sig0(W[i - 15]) + W[i - 16];
        }

        uint32_t A = IV_SHA256[0], B = IV_SHA256[1], C = IV_SHA256[2], D = IV_SHA256[3];
        uint32_t E = IV_SHA256[4], F = IV_SHA256[5], G = IV_SHA256[6], H = IV_SHA256[7];

        for (int r = 0; r < rounds; ++r) {
            uint32_t T1 = H + Sig1(E) + Ch(E, F, G) + K_SHA256[r] + W[r];
            uint32_t T2 = Sig0(A) + Maj(A, B, C);
            H = G;
            G = F;
            F = E;
            E = D + T1;
            D = C;
            C = B;
            B = A;
            A = T1 + T2;
        }

        // Davis-Meyer feed-forward
        uint32_t target_digest[8] = {
            A + IV_SHA256[0], B + IV_SHA256[1], C + IV_SHA256[2], D + IV_SHA256[3],
            E + IV_SHA256[4], F + IV_SHA256[5], G + IV_SHA256[6], H + IV_SHA256[7]
        };

        // Exact target state before Davis-Meyer addition in Z_{2^32}
        uint32_t target_state[8];
        for (int i = 0; i < 8; ++i) target_state[i] = target_digest[i] - IV_SHA256[i];

        // 2. Build the CNF circuit
        FastCircuitSHA256 circuit;
        vector<vector<int>> msg_words(16), W_vars(rounds), round_states(rounds);
        build_sha256_circuit(rounds, target_digest, circuit, msg_words, W_vars, round_states, 8);

        // -------------------------------------------------------------
        // HONEST SPLICE HOMOTOPY (STAGE 1..3 REGISTRATION HOMOTOPY)
        // Input: ONLY the 256-bit target_digest (full black box)
        // -------------------------------------------------------------
        vector<int8_t> relaxed_phase_seed;
        if (!cnf_only) {
            relaxed_phase_seed = run_pure_homotopy_ladder(rounds, target_digest);
        }
        cout << "  Circuit: " << circuit.next_var - 1 << " variables, " 
             << circuit.clauses.size() << " clauses." << endl;
        // 3. Algebraic preprocessor: F_2 Gauss-Jordan + probing
        auto tg0 = chrono::high_resolution_clock::now();
        GF2BitMatrix gf2(circuit.next_var - 1);
        for (const auto& eq : circuit.xor_equations) {
            gf2.add_equation(eq.vars, eq.rhs);
        }

        vector<pair<int, int>> implied_units;
        vector<tuple<int, int, int>> implied_binaries;
        vector<tuple<int, int, int, int>> implied_ternaries;
        vector<tuple<int, int, int, int, int>> implied_quaternaries;
        bool consistent = gf2.eliminate(implied_units, implied_binaries, implied_ternaries, implied_quaternaries);
        auto tg1 = chrono::high_resolution_clock::now();
        double dt_gf2 = chrono::duration<double>(tg1 - tg0).count();

        cout << "  ⚡ F_2 invariants (" << fixed << setprecision(3) << dt_gf2 << "s): "
             << implied_units.size() << " units, "
             << implied_binaries.size() << " binary, "
             << implied_ternaries.size() << " ternary, "
             << implied_quaternaries.size() << " 4-linear links." << endl;

        vector<int8_t> affine_solution = gf2.extract_sample_solution();
        if (!consistent) {
            cout << "  ❌ LINEAR CONTRADICTION! UNSAT!" << endl;
            continue;
        }

        for (const auto& u : implied_units) {
            circuit.add_c({u.second ? u.first : -u.first});
        }
        for (const auto& b : implied_binaries) {
            int v1 = get<0>(b), v2 = get<1>(b), rhs = get<2>(b);
            if (rhs == 0) {
                circuit.add_c({-v1, v2}); circuit.add_c({v1, -v2});
            } else {
                circuit.add_c({v1, v2}); circuit.add_c({-v1, -v2});
            }
        }
        for (const auto& t : implied_ternaries) {
            int v1 = get<0>(t), v2 = get<1>(t), v3 = get<2>(t), rhs = get<3>(t);
            for (int mask = 0; mask < 8; ++mask) {
                int p = ((mask & 1) ^ ((mask >> 1) & 1) ^ ((mask >> 2) & 1));
                if (p != rhs) {
                    circuit.add_c({
                        (mask & 1) ? -v1 : v1,
                        ((mask >> 1) & 1) ? -v2 : v2,
                        ((mask >> 2) & 1) ? -v3 : v3
                    });
                }
            }
        }
        for (const auto& q : implied_quaternaries) {
            int v1 = get<0>(q), v2 = get<1>(q), v3 = get<2>(q), v4 = get<3>(q), rhs = get<4>(q);
            for (int mask = 0; mask < 16; ++mask) {
                int p = ((mask & 1) ^ ((mask >> 1) & 1) ^ ((mask >> 2) & 1) ^ ((mask >> 3) & 1));
                if (p != rhs) {
                    circuit.add_c({
                        (mask & 1) ? -v1 : v1,
                        ((mask >> 1) & 1) ? -v2 : v2,
                        ((mask >> 2) & 1) ? -v3 : v3,
                        ((mask >> 3) & 1) ? -v4 : v4
                    });
                }
            }
        }


        // Probing
        auto tp0 = chrono::high_resolution_clock::now();
        vector<int> probe_candidates;
        for (int i = 0; i < 16; ++i) {
            for (int b = 0; b < w; ++b) probe_candidates.push_back(msg_words[i][b]);
        }
        VerifiedCDCL probe_solver(circuit.next_var - 1, circuit.clauses, 42, 100, nullptr, 0, {}, {}, &circuit.all_carry_vars);
        vector<int> found_probe_units;
        int p_res = probe_solver.probe_literals(probe_candidates, found_probe_units);
        if (p_res == -1) {
            cout << "  ❌ PROBING DETECTED ROOT-UNSAT!" << endl;
            continue;
        }
        auto tp1 = chrono::high_resolution_clock::now();
        double dt_probe = chrono::duration<double>(tp1 - tp0).count();

        cout << "  ⚡ Probing invariants (" << fixed << setprecision(3) << dt_probe << "s): " 
             << found_probe_units.size() << " nonlinear units." << endl;

        for (int u : found_probe_units) {
            circuit.add_c({u});
        }

        // Export reference CNF for independent verification (Kissat / CryptoMiniSat)
        string cnf_filename = "sha256_" + to_string(rounds) + "rounds.cnf";
        export_dimacs_cnf(cnf_filename, circuit.next_var - 1, circuit.clauses);
        if (cnf_only) {
            cout << "  🛑 Stopped by --dump-cnf flag. Solver was not run." << endl;
            continue;
        }

        // 4. Launch the multithreaded solver
        cout << "  🚀 [ASSAULT]: Searching for a preimage on " << hardware_threads << " threads..." << endl;
        auto t0 = chrono::high_resolution_clock::now();
        double timeout = (custom_timeout > 0.0) ? custom_timeout : ((rounds <= 16) ? 30.0 : ((rounds <= 18) ? 180.0 : ((rounds <= 19) ? 3600.0 : 3600.0)));
        auto result = run_portfolio_sha256(circuit.next_var - 1, circuit.clauses, hardware_threads, timeout, msg_words, round_states, W_vars, circuit.recorded_carries, circuit.all_carry_vars, affine_solution, relaxed_phase_seed);
        auto t1 = chrono::high_resolution_clock::now();
        double dt = chrono::duration<double>(t1 - t0).count();

        if (result.verdict == 1) {
            cout << "  [WINNING THREAD " << result.winner_thread << "] 🏆 SOLVED IN " << fixed << setprecision(4) << dt << " s!" << endl;
            cout << "  [STATS]: Conflicts: " << result.conflicts 
                 << ", Decisions: " << result.decisions << endl;

            uint32_t solved_M[16] = {0};
            for (int i = 0; i < 16; ++i) {
                for (int b = 0; b < w; ++b) {
                    int v = msg_words[i][b];
                    if (result.solution[v] == 1) solved_M[i] |= (1U << b);
                }
            }

            // Verification against reference SHA-256
            uint32_t test_W[64] = {0};
            for (int i = 0; i < 16; ++i) test_W[i] = solved_M[i];
            for (int i = 16; i < rounds; ++i) {
                test_W[i] = sig1(test_W[i - 2]) + test_W[i - 7] + sig0(test_W[i - 15]) + test_W[i - 16];
            }

            uint32_t cA = IV_SHA256[0], cB = IV_SHA256[1], cC = IV_SHA256[2], cD = IV_SHA256[3];
            uint32_t cE = IV_SHA256[4], cF = IV_SHA256[5], cG = IV_SHA256[6], cH = IV_SHA256[7];

            for (int r = 0; r < rounds; ++r) {
                uint32_t T1 = cH + Sig1(cE) + Ch(cE, cF, cG) + K_SHA256[r] + test_W[r];
                uint32_t T2 = Sig0(cA) + Maj(cA, cB, cC);
                cH = cG;
                cG = cF;
                cF = cE;
                cE = cD + T1;
                cD = cC;
                cC = cB;
                cB = cA;
                cA = T1 + T2;
            }

            bool ok = ((cA + IV_SHA256[0]) == target_digest[0] &&
                       (cB + IV_SHA256[1]) == target_digest[1] &&
                       (cC + IV_SHA256[2]) == target_digest[2] &&
                       (cD + IV_SHA256[3]) == target_digest[3] &&
                       (cE + IV_SHA256[4]) == target_digest[4] &&
                       (cF + IV_SHA256[5]) == target_digest[5] &&
                       (cG + IV_SHA256[6]) == target_digest[6] &&
                       (cH + IV_SHA256[7]) == target_digest[7]);

            cout << "  Recovered 512-bit message block M[0..15]:" << endl;
            for (int i = 0; i < 16; ++i) {
                cout << "    M[" << setfill(' ') << setw(2) << i << "] = 0x" 
                     << hex << setfill('0') << setw(8) << solved_M[i] << dec << endl;
            }
            if (ok) {
                cout << "  SHA-256 Davis-Meyer verification: ✅ 100% DIGEST MATCH!" << endl;
                string sol_filename = "sha256_" + to_string(rounds) + "rounds_solution.txt";
                ofstream sol_out(sol_filename);
                if (sol_out.is_open()) {
                    sol_out << "VERDICT: SAT\n";
                    sol_out << "ROUNDS: " << rounds << "\n";
                    sol_out << "TIME_SEC: " << dt << "\n";
                    sol_out << "WINNING_THREAD: " << result.winner_thread << "\n";
                    sol_out << "CONFLICTS: " << result.conflicts << "\n";
                    sol_out << "DECISIONS: " << result.decisions << "\n";
                    sol_out << "MESSAGE_HEX: ";
                    for (int i = 0; i < 16; ++i) sol_out << hex << setfill('0') << setw(8) << solved_M[i];
                    sol_out << dec << "\n";
                    sol_out.close();
                    cout << "  💾 [SAVED]: Result written to file " << sol_filename << endl;
                }
            } else {
                cout << "  ❌ VERIFICATION ERROR!" << endl;
            }
        } else if (result.verdict == 0) {
            cout << "  ❌ UNSAT PROVEN (" << dt << " s): formula inconsistency rigorously proven at the root level." << endl;
            break;
        } else {
            cout << "  🛡️ STOP: Timeout (" << dt << " s). Round " << rounds << " held its ground." << endl;
            break;
        }
    }
}

#ifndef SHA256_SOLVER_NO_MAIN
int main(int argc, char* argv[]) {
    int target_r = 18;
    bool cnf_only = false;
    double custom_tmo = 0.0;
    uint32_t target_seed = 0;
    if (argc > 1) {
        target_r = atoi(argv[1]);
    }
    for (int i = 2; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--dump-cnf") {
            cnf_only = true;
        } else if (arg == "--random-target") {
            random_device rd;
            target_seed = ((uint32_t)rd() << 16) ^ (uint32_t)rd();
            if (target_seed == 0) target_seed = 123456789;
        } else if (arg == "--seed" && i + 1 < argc) {
            target_seed = (uint32_t)atoll(argv[++i]);
        } else if (isdigit(arg[0])) {
            custom_tmo = atof(arg.c_str());
        }
    }
    cout << "  Launch parameter: target rounds = " << target_r;
    if (custom_tmo > 0.0) cout << ", timeout = " << custom_tmo << " s";
    if (target_seed != 0) cout << ", random target seed = " << target_seed;
    if (cnf_only) cout << " (CNF EXPORT MODE)";
    cout << endl;
    run_sha256_experiment({target_r}, cnf_only, custom_tmo, target_seed);
    return 0;
}
#endif
