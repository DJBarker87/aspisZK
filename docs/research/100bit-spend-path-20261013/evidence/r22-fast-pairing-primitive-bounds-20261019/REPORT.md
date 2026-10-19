# R22 fast-pairing primitive bounds

Four new focused lemmas cover plain multiplication sites used in the current `fast_pairing.rs` formulas: every widened U32-by-U32 product fits U64; multiplying any partial-fold result by a coefficient at most three fits U64; the `3*P` and `2*P²` constant products fit U64; and the actual wrapping partial fold is below 10,737,418,240 on every stored U64 input. Each covered checked multiplication is total and equal to its wrapping result.

These are reusable arithmetic leaves for R22, not an extraction or refinement of `Q::raw`, `Q::mul`, the dot accumulator, or their callers. In particular this packet does not infer the canonicality of the private Q representation from Rust visibility. The function bodies and caller guards must still be connected to these lemmas. Explicit wrapping sums/subtractions already state their intended semantics; the remaining caller, counter/index and reducer correspondence obligations are separate.

`R22FastPairingPrimitiveBounds` passed on the NUC: exit 0, 1.705 s, process peak RSS 2,627,772 KiB, cgroup peak 309,395,456 bytes, swap peak 0. All four printed axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. The scope used MemoryHigh=512 MiB, MemoryMax=1 GiB, MemorySwapMax=0; no OOM or cap increase occurred.

The exact source revision, compiler/source/object/import hashes, ordered roots, command, admission, reservation, GNU-time and receipt are retained. All 24 payload hashes were checked on publication. Archive SHA256: `80a03e045790d314171913240dfa4513dfc05479588831824cd37903404aebbd`. No full manifest replay or held commitment-layer work occurred.
