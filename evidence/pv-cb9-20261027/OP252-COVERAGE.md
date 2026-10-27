# op252 coverage correction

The first op252 run uses the dependency declaration `aspis_r1_cost_probe::weights::Weights::new`. Charon records its real Structured body, but Aeneas emits empty Types/Funs modules (retained as op252-empty-*.lean.txt). Exit 0 is not extraction coverage and earns no source-law credit.

The existing source-proof/lib.rs contains a cfg(kani) path module `current_weights` pointing directly to ../source/crates/aspis-r1-cost-probe/src/weights.rs. No file copy or implementation edit was made. The second extraction selects `pv_cb3_source::current_weights::Weights::new` and its existing helper module; this is a changed extraction root after an empty-output success, not an unchanged refusal retry. Current-crate Weights::new then receives `ProverRwRngExtractor006: fail-closed preflight: structured Drop requires destructor semantics`.

The field arithmetic and all complete Result/error paths remain unproved. No cast, desired-output premise, opaque callback alias, reference implementation, or Kani arithmetic gate was introduced.
