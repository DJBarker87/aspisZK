# Candidate: unroll four-limb canonical-Q validation

This is an isolated source candidate; it does not modify the frozen production Rust. It changes only `canonical::Q::from_limbs` from `x.iter().all(|&v| v < P)` to ordered array destructuring and `a < P && b < P && c < P && d < P`. The existing source `checked_q` call remains byte-identical.

The candidate preserves output and rejection semantics for every `[u32; 4]`: both implementations accept iff each of the four coordinates is below `P`; the conjunction keeps the original left-to-right short-circuit order. The predicate has two semantic classes per coordinate, so the 16 truth assignments exhaust the four-coordinate predicate partition. Separate tests exercise boundary representatives (`0`, `1`, `P-1`, `P`, `P+1`, `u32::MAX`) at each position and 250,000 deterministic arbitrary arrays against the Rust standard-library `Iterator::all` reference.

This offers a refactoring candidate that removes `Iterator::all` from `Q::from_limbs`. The Lean source-cut packet proves the emitted candidate method has exactly the same full `Result (Option Q)` behavior as the retained state-threaded `allRun` model. It does not prove equivalence for the frozen production method or the Rust std `Iterator::all` implementation. Adoption still requires a reviewed source change and caller-level equivalence review.

Run `python3 check_candidate.py`, then `rustc --edition=2021 --test tests/iterator_all_equivalence.rs -O -o /tmp/s4-checked-q-all-equivalence && /tmp/s4-checked-q-all-equivalence`.
