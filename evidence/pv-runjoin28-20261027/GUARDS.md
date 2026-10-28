# Preparation guard inventory (source inspection; proof status explicit)

`PV_Src_NativeInput.run` calls only `compile_forest_from_copies` (Rust
pair_forest_trace.rs:265–388). `CompilerDomain28.Path` exposes its complete
primitive/branch success path. It does not describe the wrappers at390–488.

The actual wrappers additionally perform, in order:

1. `lane_root`: validate/hash the pair leaf, then twenty path parents.
2. Validate public data with its anchor replaced by the lane root: nonzero
pool/domain, anchor_sequence at most2^20, canonical lane-root/nullifier,
canonical asset; then canonical recipient/change (transfer), or nonzero
amount below2^30, nonzero destination, canonical change (withdrawal).
3. `validate_common` with the context anchor also replaced: matching runtime
pool/domain/sequence/asset, nullifier not already spent, canonical key/salt/
membership siblings, input positive and below2^30, membership index below2^20,
valid/spendable pair leaf. The original runtime anchor is overwritten, not
checked against the global forest anchor.
4. Snapshot pool/domain equals public pool/domain.
5. Transfer: recipient and change both positive and below2^30, checked sum
exactly equals input. Withdrawal: change positive and below2^30, amount plus
change checked sum equals input.
6. The inner compiler path, including selected input/pair/lane/nullifier/
recipient/change/output-pair checks, live append, canonical super-root
siblings, global anchor, bank existence and row validation.

Guard failures return the first encountered error, not necessarily that of
a later failing guard. Converse lemmas must include prior-prefix success.

Additional semantic rejection candidate: ZeroRecipient28 keeps positive
change and the original checked change sentinel, but admits a zero recipient.
Its Lean admission is pending compilation. No native outcome is yet claimed.

Potential representation issue requiring investigation: `late_append` uses
`IncrementalMerkleTreeV1::from_parts_with_empty_roots`, whose validator checks
inactive frontier slots against empty roots and reconstructs the root. It
has no explicit canonical-digest test for active frontier words. The separate
snapshot codec validator DOES check all frontier words; it is not called by
these compiler wrappers. This is source inspection, not a checked successful
preparation counterexample. Do not infer the required HonestInput frontier
property merely from the word “NonCanonicalFrontier” in the tree error enum.

A focused optimized native GUARD probe is prepared to investigate the active
frontier issue at index1 with frontier[0]=[P;8], a freshly reconstructed
matching root, original positive input/amount/change, and no cached payload
mutation. It calls the actual outer withdrawal compiler and snapshot codec.
This is investigation of requirements1–2, not native RunJoin/refinement work
under requirement4. No outcome has yet been observed.
