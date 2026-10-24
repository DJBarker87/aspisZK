# Response-driven checkpoint repair

Status: focused source work; both deployed security targets remain unestablished.

## Interface diagnosis and before/after

Historical `Port8EFF_CheckpointCode.program D hash code` evaluates D.digest and
uses `.ask address (fun _ => program ... (k nativeBytes))`. Its value theorem
holds for every H precisely because the reply is discarded. Its effects theorem
requires `Oracle D hash H`, whose COMPLETE definition is:

    ∀ parts digest, D.digest hash parts = ok digest →
      stateOf digest = H (flatten parts)

This constrains successful calls only; it asserts neither totality nor failure
correspondence. The retained Code has existentially typed Result steps and
Digest=`Aeneas.Std.Array U8 32#usize`; State=`Fin 32 → Fin 256`.
Outer Result.fail/div differs from an ordinary returned Rust Err. The historical
StateT run discards the prefix on an outer failure. These facts are unchanged.

Before: fixed D, arbitrary H, value equal to the fixed-D native return;
ordered success effects require Oracle D hash H.
After: fixed D supplies ONLY its existing primitive success/fail/div policy;
`Port9OR_Code.program D hash code` is fixed before H, and successful reads
continue on `Port9OR_Reply.digest reply`. For EACH H, `native D H` interprets
the native primitive by replacing each successful digest with the exact encoded
H reply and retaining the original fail/div policy. `correspondence` equates
the fixed Program's full return AND ordered effects with `trace (native D H)`
on ALL inputs/outcomes, with no Oracle, acceptance or desired equality premise.
The pointwise native dictionary is NOT passed into the sampled experiment.

`state_digest` and `digest_state` prove both exact finite representation round
trips, without truncation or admission assumptions. `trace` preserves successful
read prefixes even when the source later fails/diverges; inner Err, duplicates,
and all branch-selected suffixes are ordinary tree control. Failed primitive
calls emit no successful digest observation, matching the inherited policy.
No query is invented for an unexecuted call. This is an ideal-oracle source
interpretation, not equality of real SHA256 with every H.

## Concrete source instance and trust

`Port9OR_Bodies.reader_value/reader_effects` instantiate the current emitted
Port8EFF_NativeReader with Port6CK_Ops at its concrete source types.
`writer_value/writer_effects` instantiate the existing checkpoint writer.
Only the existing error carrier conversion is applied. Their source trees,
primitive/adoption/extraction boundaries and error policy are reused, unchanged.
The conversion and interpreter proofs are new. This is not an ELF identity gate.

`Port9OR_Law.source_primitive` interprets the exact already-emitted SolanaDigest
wrapper through its existing hashv callee substitution, retaining errors. It does
not postulate a whole-caller/native equivalence or a new extraction axiom.
`reader_lazy` states the exact finite-support lazy law for ANY rational
observable of the reader's full log AND Result: its support and probability
space come from ONE fixed Program. Pointwise native interpretation occurs only
inside that law's integrand. There is no conditioning or H-indexed sampled
experiment. This local law does not prove the source security event domination.

The original Port8 files and conditional evidence remain historical/local facts;
none was edited, and no discarded-response claim is silently promoted.

`Port9OR_Checksum.checksum_branches/checksum_reject` prove a concrete
current-reader checksum response dependency at the installed comparison leaf:
a matching exact reply takes the decoder branch, any distinct reply rejects
before the decoder suffix. `discarded_reply` retains the Port8 counterexample
schema when the native byte array differs from the sampled reply. The defect
cannot pass these new source statements. Focused successful receipts:
003 Reply,004 Code,006 Bodies,007 Bridge,008 Driver,009 Budget,012 Law,016
Checksum. Failed 001/002,005,010/011,013..015 are preserved elaboration proofs,
not accepted axioms. No resource failure or unchanged retry occurred.
