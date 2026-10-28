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

Additional checked semantic rejection: ZeroRecipient28 keeps positive change
and the original checked change sentinel, but admits a zero recipient
(Lean38173). The optimized native400/0/400 transfer probe returns
Err(Conservation); see pv28-zero-recipient-01/receipt.json.

Checked raw-wrapper representation issue (FINDING.md): `late_append` uses
`IncrementalMerkleTreeV1::from_parts_with_empty_roots`, whose validator checks
inactive frontier slots against empty roots and reconstructs the root. It
has no explicit canonical-digest test for active frontier words. The separate
snapshot codec validator DOES check all frontier words; it is not called by
these compiler wrappers. The native probe confirms successful preparation, and Lean38158 proves
exclusion from HonestInput for every payload with this raw frontier. This
does not show that a canonical encoder produces such arguments. Do not infer
canonical limbs from the tree error name “NonCanonicalFrontier”.

The focused optimized native GUARD probe investigated the active
frontier issue at index1 with frontier[0]=[P;8], a freshly reconstructed
matching root, original positive input/amount/change, and no cached payload
mutation. It calls the actual outer withdrawal compiler and snapshot codec.
This is investigation of requirements1–2, not native RunJoin/refinement work
under requirement4. It passed with a fresh successful compilation and separate codec rejection.

Retained resource failure38162: direct reuse of pair_valid for a first-
commitment update caused kernel memory exhaustion at ZeroRecipient28.valid
(peak7,340,810,240bytes). Replacement: first prove PairValidity28.replace_first
with symbolic PairLeaf fields, then instantiate it. The first commitment is
irrelevant to occupancy validity. No concrete hash is normalized, no cap is
raised, and the failed source is not rerun unchanged.

D188 per-function boundary: the new compiler-domain/error proofs split only
the already identified extracted compiler control flow. Its super-root scan
reads shared elements; dropping the exhausted iterator state does not discard
a data write. The archived one-step tree validator draft threads the local result
explicitly; it has no mutable data-borrow restoration. No new Rust-source law
for a mutable-iterator write body is claimed. Existing source/helper fidelity
associations are reused as recorded in the predecessor reports; no XR source
or object is imported or copied.

Optional active_slot_skipped draft: attempts38175/38176/38178 failed because
kernel reduction cannot evaluate the platform-sized scalar representation.
The latest symbolic scalar-value draft was not launched (38179 refused).
It is retained under drafts/PV_RunJoin_ActiveFrontier28-symbolic.lean.txt and
is NOT an accepted theorem. It is omitted from DomainSupport28, which checks
the independent fresh-payload and canonical-encoding lemmas. The source guard
inspection, native validation result and checked frontier exclusion do not
rely on this draft. This ordinary candidate failure is not the stopping reason.
