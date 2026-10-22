# Constructive powers-to-S9 scalar-factor join

`powers_trace_scalar_factor_constructively_s9` uses one successful P6 N=4 powers trace and one successful `kpowers` result. It derives canonical reads of the same mapped `p` array and `f` array, constructs successful `scalar_factor` execution via extracted-fold totality, and passes that exact returned output to the retained S9 identity theorem. The helper success/output is no longer a free premise.

The powers trace, `kpowers` success, p-array map, seed, and S9 model inputs remain explicit. The theorem does not establish `Weights::pair` source assignments or Rust `from_fn` correspondence.

The final compile used Lean 4.32 arm64 with `-j1 -M4400`; exit 0, 16.93 seconds, peak RSS 3,212,394,496 bytes, swap 0; audited axioms are standard only. `receipts/launch.json` records exact argv and import pins. The first setup-only missing-import attempt is retained as a diagnostic.
