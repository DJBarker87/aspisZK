# S6 complete accepted payment inverses — 2026-10-23

S6 OPEN; target not yet established. This closes both complete 216-byte
payment accepted inverses for the concrete complete codec reference. It does
not close the 1880-byte forest inverse or actual SDK/caller port. Source scope,
historical/current compatibility and release pins remain those recorded in
S6-ENCODER-TOTALITY-20261023.md and its source compatibility packet.

## Exact enclosing statements

`AspisS6SourceCodec.PaymentContents.transfer_accepted_inverse` and
`withdrawal_accepted_inverse` establish, for arbitrary input slices and full
native public records of the corresponding variant:

    decode bytes = ok (RustResult.Ok public) →
      ∃ encoded : Array U8 216,
        encoded.val = bytes.val ∧ encode public = ok (RustResult.Ok encoded)

The sole enclosing premise is the actual complete decoder return. No fixed
input length, canonicality, encoder acceptance, validator success, common-value
binding or successful child operation is independently assumed. Those facts
come from the checked actual decoder frames and its concrete validator calls.
The record carriers, all fields and source error/control paths are unchanged.
This is ACCEPTED-ONLY inverse correspondence, composed with the prior TOTAL
payment decoder and encoder theorems. It does not claim malformed inputs accept.

Before composition, `transfer_write`/`withdrawal_write` require the exact common
projection return and successful concrete validator return. The two enclosing
inverse theorems discharge both from `transfer_frames`/`withdrawal_frames` on
this same decoder execution. No arbitrary Ops dictionary or simplified public
carrier is introduced. Complete native Array/Slice/public/error types are reused.

## Concrete source details retained

The common writer writes bytes0..6 and leaves byte7 untouched. The actual
payment callers initialize the entire216-byte buffer to zero. The proof
retains that behavior rather than adding a fictitious byte7 write. Transfer
also leaves bytes148..151 at their initialized values; the frozen canonical fee
is zero. A symbolic zero-word theorem proves those four fee bytes, without
enumerating field values. Withdrawal explicitly writes its actual amount.

`common_contents` describes the actual common writer's 148-byte prefix and
remaining68 initialized bytes. Its contract is generalized over the initial
native array, with the byte-content conclusion conditional on that array being
the actual caller's zero initialization. The earlier fixed-zero formulation
and this conditional formulation give the same guarantee at the actual call.
Existing totality on arbitrary initial arrays is retained separately. The
source caller discharges initialization by reflexivity; no such premise leaks
into either enclosing accepted inverse.

Symbolic list frame theorems compose the actual point and chunk writes.
Header/common slice frames telescope to the first148 input bytes; the complete
payment tail then reconstructs every remaining byte. Digest frame equality
uses the actual concrete digest encoder return and its checked32-byte inverse.

## Focused validation and failure replacement

`S6SourcePaymentAcceptedInverseV1`, attempt
`s6-source-payment-accepted-inverse-v3`: exit0, wall14.242612s,
peak RSS2244886528 bytes, zero swap. Both enclosing inverses and the fee lemma
print only propext, Classical.choice and Quot.sound.

The first writer applications hit the default recursion limit. Diagnostic
counters showed repeated List.replicate/List.rec/Nat.rec reduction. No cap or
resource option was raised. The replacement keeps the initial native array
symbolic through the WP-to-existential bridge, then instantiates the checked
source caller's initialization beneath equality. This avoids eagerly reducing
the concrete216-byte initial buffer while retaining the identical source body.
`common_output` is the checked bridge. A dependent prefix-frame target was
recompiled once after this interface change; no unchanged manifest replay ran.
Earlier failed attempts and diagnostic/probe output are excluded evidence only.

Selected receipts are listed in `s6-payment-inverse-targets.json` beneath
`evidence/s126-current-caller-20261021`. Every receipt records source revision,
exact target/source/tool/import pins, command, exit, wall, RSS, swap and axioms.
`s6-payment-inverse-import-pins.json` hashes the dependency objects without
shipping binaries. Source-only evidence audit:

    python3 -B tools/s6-full-forest-roundtrip-20261023/check-payment-inverse.py

All accepted local checks used the atomic Lean lock, -j1 and -M4400 and reported
zero swap. No native_decide, custom axiom, admitted proof or resource override
is installed. Rust source and production/release artifacts were not changed.

## Remaining enclosing obligations

- Snapshot and afterstate accepted inverses, followed by the enclosing late
  statement and full1880-byte forest accepted inverse.
- Remaining decoder totality beyond the complete digest/payment boundaries.
- Contextual transport of prior verified reference loop transformations,
  actual allocation/runtime/account semantics, and the current owned-adapter/H5
  first/first_decoded/stage1 source port with its actual returned values and
  ordered reads, using release observer None.
- S1 original whole prepared_claim/Prepared/caller execution with actual Std/P6
  interpretation. Prior gamma-scratch and joint challenge trace results retain
  their recorded premises; this payment result does not close them.

S2 remains with its transferred owner. No S2/S3/S9/S4/S5 track was edited.
Candidate adoption, if needed, still requires relevant equivalence/contextual
and source/artifact/proof re-pin gates. The 100-bit target is unchanged.
