# SHA-256 cryptanalysis: a C++ CDCL solver and algebraic inversion for 18-20 rounds

This repository contains experiments on round-reduced **SHA-256 (FIPS 180-4 / RFC 6234)**. It has four parts:

1. **`sha256_engine`**: a SAT solver written from scratch in C++17, with no dependencies. It learns clauses, runs F2 Gauss-Jordan elimination as a preprocessing pass, and shares short lemmas between 12 threads through a mutex-protected ring buffer (16,384 slots).
   * 18 rounds: solved in 3.4-5.8 s (11,451 conflicts) on my benchmark target.
2. **A measurement of where plain CDCL stops working (18 to 19 rounds).** An 11.75-hour run on 19 rounds reached 241,236,992 conflicts without finding a solution, about 20,000 times more than for 18 rounds. The likely cause is the nonlinear Ch multiplexers combined with carry propagation.
3. **Local verification of the algebraic method of Sebastian R. Wain** (arXiv:2611.00512), which builds on context shaping by K. S. Basra.
   * 19 rounds: preimage in 298.6 s on one CPU core.
   * 20 rounds: preimages under standard FIPS 180-4 padding (55-byte messages, terminating `0x80`, zero padding, 64-bit length `0x01b8`). I verified 46 distinct preimages.
4. **`sha256_engine/pre18.c`: my adaptation for 18 steps and arbitrary targets.** With Wain's context shaping at 18 steps only two message-schedule equations remain (W16, W17). The third Q^-1 inversion can be dropped, and a4 = a3 closes the Maj identity when D = 0. I am not aware of an earlier published practical 18-step inversion for arbitrary targets.
   * A 2^28 table takes about 11 s to build (about 1 GiB RAM). Each further target then takes under 0.1 s of search.
   * The method is derived from Wain (MIT) and Basra's context shaping. The 18-step reduction is ours. Padded 18-step mode is not supported.

The next goal is to combine the two approaches for 21+ rounds: use context shaping to remove the nonlinear multiplexers, then pass the remaining carry constraints to the CDCL engine. This is a plan, not a result.

---

## Quick verification

The script needs only Python 3:

```bash
python verify.py
```

Expected output:
```text
==============================================================================
  SHA-256 PREIMAGE VERIFICATION SUITE (18, 19, 20 ROUNDS)
  RFC 6234 / FIPS 180-4 Standard Compliance & Algebraic Cryptanalysis
==============================================================================

[+] 1. Verifying 18-Round CDCL + F2-Kernel Preimage...
    Target:   2d05c038dd424920ed69170065b45518d57d36d31b398b2826dce7786773bf25
    Computed: 2d05c038dd424920ed69170065b45518d57d36d31b398b2826dce7786773bf25
    Status:   [PASS] 18 Rounds Verified (Solved in 5.8s)

[+] 2. Verifying 19-Round Algebraic Preimage (Wain/Basra Method)...
    Target:   688162267e6388565e498e0d564a18c81d97ebe01f744ce09fb7fc476339dae6
    Computed: 688162267e6388565e498e0d564a18c81d97ebe01f744ce09fb7fc476339dae6
    Status:   [PASS] 19 Rounds Verified (Solved in 298s)

[+] 3. Verifying 20-Round Standard Padded Preimage ('abc' target)...
    Target:   ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
    Computed: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
    Padding:  W13=0xc6822680 (&0xff=0x80), W14=0x0, W15=440 bits -> VALID
    Status:   [PASS] 20 Rounds Padded Verified

==============================================================================
  🎉 ALL 18, 19, AND 20 ROUND PREIMAGES SUCCESSFULLY VERIFIED (100% PASS)
==============================================================================
```

To check all 46 witnesses (padded and unpadded):
```bash
python srw_pre19/verify_all_witnesses.py
```

---

## How the two approaches work

### 1. The CDCL engine (18 rounds in 3.4 s)

`sha256_engine/sha256_solver.cpp` encodes 18 rounds of SHA-256 as 17,936 Boolean variables and 71,706 clauses. It adds three things on top of a basic CDCL solver:

* **F2 Gauss-Jordan preprocessing.** A single pass derives 483 unit, 1,092 binary, 3,492 ternary and 1,045 four-variable linear parity constraints.
* **Lemma sharing.** 12 worker threads use different decision heuristics and exchange short learned clauses (up to 3 literals, or LBD <= 2) through the ring buffer.
* **Fixing the state at step 16.** Registers A..F are set directly to the target constants, so unit propagation can resolve the remaining freedom within seconds.

### 2. Why 19 rounds is hard for plain CDCL

Going from 18 to 19 rounds adds only about 4% more variables (17,936 to 18,688), but the conflict count grows roughly 20,000-fold. In a continuous 12-thread run of 42,301.3 s (11.75 h) the solver made 241,236,992 conflicts and 344,588,288 decisions and exchanged 1,097,370 lemmas, with no solution found.

Going back three more rounds produces a chain of Ch multiplexers:

$$H_{18} = C_{18} - W_{18}$$
$$ch_{17} = E_{17} \ ? \ F_{17} : H_{18}$$
$$H_{17} = C_{17} - W_{17} - ch_{17}$$
$$ch_{16} = E_{16} \ ? \ H_{18} : H_{17}$$
$$H_{16} = C_{16} - W_{16} - ch_{16}$$

My guess is that the modular carries inside these nested multiplexers defeat unit propagation, but I have not isolated this experimentally.

### 3. The algebraic method (Wain / Basra)

This approach does not treat SHA-256 as a generic SAT formula. It uses the structure of the round function:

* **The a-sequence determines the state.** Because the state registers are shifted copies of each other, the full 8-word state at step s follows from four consecutive values of register a:
  $$E(s) = a_s - \Sigma_0(a_{s-1}) - \text{Maj}(a_{s-1}, a_{s-2}, a_{s-3}) + a_{s-4}$$
* **Context shaping.** Setting e_9 = e_10 = 0xFFFFFFFF gives Ch(0xFFFFFFFF, y, z) = y, so the multiplexers in the tail become linear.
* **Inverting Q_0.** The message-schedule equations for W_16..W_18 reduce to equations in Q_0(u) = sigma_0(u) - u. These are inverted by lookup in a precomputed hash table (2^27 entries, about 512 MB).

---

## Complexity and timing (20 rounds)

| Target | Complexity | Hardware | Wall-clock time |
|---|---|---|---|
| 18 rounds (CDCL, benchmark target) | ~2^13.5 | 12-thread CPU | 3.4-5.8 s |
| 18 rounds (algebraic, arbitrary target) | table build + a few hundred chains | 1 CPU core (~1 GiB RAM) | ~11 s table, < 0.1 s per target |
| 19 rounds (algebraic) | ~2^29.6 | 1 CPU core (0.5 GB RAM) | 19.5-298 s |
| 20 rounds (unpadded) | ~2^38.1 | 16 vCPU | ~21 min |
| 20 rounds (FIPS padded) | ~2^46.6 | 1x NVIDIA L4 / RTX 4090 | 9-22 hours (or ~191 CPU-hours) |

All 46 precomputed witnesses in this repository were verified on local hardware. Timings are from my own runs; I have not done a controlled head-to-head against Kissat/CaDiCaL with identical encodings, so these numbers are not a general performance claim.

---

## Build and usage

### CDCL solver (18 rounds)
```bash
g++ -O3 -std=c++17 sha256_engine/sha256_solver.cpp -o sha256_engine/sha256_solver
./sha256_engine/sha256_solver 18 30
```

### 18-step engine for arbitrary targets
```bash
gcc -O3 -march=native sha256_engine/pre18.c -o sha256_engine/pre18
T=$(python3 -c "import hashlib;print(hashlib.sha256(b'my label').hexdigest())")
./sha256_engine/pre18 comp $T 28 1 3 26
```

### 19-round algebraic solver
```bash
gcc -O3 -march=native srw_pre19/src/pre19.c -o srw_pre19/src/pre19
./srw_pre19/src/pre19 comp <TARGET_HEX_256> 27 1 3 26
```

Parameters:
* `27`: table size, 2^27 entries (about 512 MB RAM).
* `1`: random seed / worker thread ID.
* `3`: k_max, the context expansion threshold.
* `26`: log2 of the chain budget per context (2^26).

The targets for `pre18` and `pre19` are 256-bit values for the reduced-round function. A solution is a preimage under 18 or 19 steps, not under full 64-step SHA-256.

---

## Plans for 21+ rounds

I want to build a hybrid solver:

1. Use algebraic context shaping as a first reduction step.
2. Pass the remaining nonlinear constraints to the parallel CDCL engine.
3. Scale the tables up (2^31 entries, more than 32 GB RAM) to try 21 and 22 rounds.

None of this is implemented yet.

### Compute fund (goal: $300)

Larger experiments need a machine with a lot of RAM and GPUs. If you want to help pay for it, donations are accepted in Monero (XMR):

```text
46Z6K6aZgXhJdA3bgZyX2UAQ6Pm3XeZHH5KSnDv8DAxdbEytJCpuYLdhcLT7S3k7h9P8bu4LeKSp2RprCNRfBwS9R3Xqvtp
```

![Monero donation QR code](docs/xmr-qr.png)

---

## References

If you use this work, please cite:

```bibtex
@misc{wain2026sha256,
  author    = {Sebastian R. Wain},
  title     = {Practical Preimages for 19- and 20-Step SHA-256 with Standard Padding},
  year      = {2026},
  eprint    = {arXiv:2611.00512},
  archivePrefix = {arXiv},
  primaryClass  = {cs.CR}
}

@software{sha256_hybrid_breakthrough,
  author    = {nxvr443},
  title     = {SHA-256 Cryptanalysis: Custom C++ CDCL Engine \& Algebraic Inversion Suite},
  year      = {2026},
  url       = {https://github.com/nxvr443/sha256-cryptanalysis-20rounds}
}
```

---

## License

The original code in this repository (`sha256_engine/`, verification scripts, documentation) is licensed under the **GNU Affero General Public License v3.0 (AGPL-3.0)**. See `LICENSE` in the repository root.

The vendored directory `srw_pre19/` contains Sebastian R. Wain's algebraic solver under the **MIT License** (see `srw_pre19/LICENSE`). It is included with attribution to Wain and K. S. Basra, and the root AGPL-3.0 license does not apply to it.

`sha256_engine/pre18.c` is my adaptation of that framework. My 18-step reduction is AGPL-3.0, and the derived Wain/Basra parts remain MIT, with the original notice kept in the file header.
