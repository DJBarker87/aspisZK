# S4 PR#10 candidate source-binding checkpoint

This source-only checkpoint checks that the exact three Rust blobs proposed by PR#10 are the ones covered by the retained S4 candidate source/body evidence. It also pins the unchanged `candidate.rs` and `verifier.rs` callers, checks the actual `query_values` opening-then-`four_dots` callsite, and confirms that `Prepared::new` assigns `powers::<29>(gamma)` to the caller-owned scratch array.

The checker reconstructs the entire proposed `weights.rs` blob by applying the accepted early-return powers patch to the exact `b2727acd3` baseline file. The reconstructed bytes and hash match PR#10's `28b558...` blob. It also runs the accepted S1 source-model checker, so the generated early-powers theorem is selected by the actual N=29 caller slot represented by the prepare and tx2 source cuts; no separate success or desired-array premise is added by this packet. It reuses the existing early-powers result, fast-dots endpoint, checked-Q binding, query-callsite, and prepare-parent checkers rather than recompiling their Lean proofs.

Run from the repository root:

```sh
python3 docs/research/100bit-spend-path-20261013/evidence/s4-pr10-source-binding-checkpoint-v1-20261022/check_packet.py
```

The checkpoint is for the isolated candidate branch at the exact commit and hashes in `manifest.json`. It does not establish the frozen Rust `core::array::from_fn` correspondence, all caller leaf installations, SBF artifact adoption, or production approval. The existing candidate CU/B1 result is not changed by this source check. No compiled artifacts are included.
