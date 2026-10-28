# NBX U05 continuation

Inherited ASF8 validator/encoder and getters retain exactly NBU_U05_BRIDGE.md’s
conditional scope and lower codec domains. No inherited theorem is re-proved.
ASQ8/op23 needs the ruling (s) instance. K050’s result-control pass is now paired by NBX_K050 under the identical
frozen/KMX configuration (final completion below). ASR8 last.

Potential op53 frame obstruction: frozen emit_result calls
program::set_return_data(&encoded) before returning Ok(()). The SDK op53 returns
only Result Unit. Ruling (s)’s no-write-outside-return condition must account
for the runtime return-data effect; purity cannot be asserted from its argument.

## Remaining U05 member ledger

| Member | Scope retained / remaining work |
|---|---|
| payment nullifier / transition_kind | inherited NBU K022/023 getter/reference bridges; unchanged |
| statement common / nullifier / transition_kind / statement_public_common | inherited NBN/NBD/NBU exact same-reference/tuple results; unchanged |
| transition_kind | inherited exact byte/error bridge; unchanged |
| ASF8 validate statement | inherited CLOSED-CONDITIONAL, exactly DigestEncodeCanonical and TransferEncode/WithdrawalEncode; no new law |
| ASF8 encode statement | inherited CLOSED-CONDITIONAL, exactly raw DigestEncode and TransferEncode/WithdrawalEncode; no new law |
| ASQ8 decode request | OPEN ruling(s) instance; NBX magic rejection/payment-window frame are partial only; complete child/frame/call-site composition still needs native evidence |
| validate_result | CLOSED-CONDITIONAL locally: NBU K050 positive paired with NBX_K050 negative; imported NBN_ResultDependency.source and NBN_ResultValidator.source retained. NBX_ResultComposition composes the SAME record and complete Result, without a successful-child premise (L113 passes) |
| validate result against statement | OPEN native/source full comparison and error-order body; ASR8 body fidelity is out of soundness scope. Nothing promotes a result-only validator to this function |
| ASR8 encode result | OPEN body bridge, out of soundness scope; exact returned byte ranges/copy composition are not proved here |
| emit_result / op53 | OPEN required instance under ruling(s); exact argument source point inspected, but runtime return-data write exceeds the literal Result Unit frame. NBX_OP53_FINDING.md; no interface/trust change |

Every inherited OPEN lower codec remains an exact condition. No LPb pass is
newly credited. Nothing here discharges the SDK/runtime/allocator/ABI/compiler/
P6 or source-to-ELF boundaries, nor establishes the deployed100-bit target.

## Completed result-control pair and composition

validate_result is now **CLOSED-CONDITIONAL locally** by the direct hybrid P6
method, conditional exactly on the existing DigestEncodeCanonical lower law.
No successful-child/caller premise, adapter law or new dictionary is added.

- Reused positive NBU_K050: exit0,0/447 failed. NBX_K050 runs the requested
  NBU_result_control_negative: exit1,1/447 failed. All original common source
  hashes, KMX attributes/unwind1881, limits, semantic env and frozen graph/lock
  match. Only temporary/target directory names differ. The sole source change
  between the two control bodies is assert_eq(stage,0) → assert_ne(stage,0) at
  the first lane callback. NBX_CONTROL_PAIR.json checks these facts.
- Kani prints its runtime-format placeholder at core::panicking::assert_failed_inner
  for that negative assertion panic. Its caller_location/foreign-function
  warnings are retained. This is an expected negative panic-path failure,
  not an unwinding, codegen, memory or solver-timeout failure.
- NBX_RESULT_ASSOCIATION.json checks the complete frozen validate_result body
  against NBU_result_cut under EXACTLY two callee-name substitutions: lane and
  afterstate encoder. The common record, original references, first-error
  order, result and stage order are the same as the positive native control.
- Imported NBN_ResultDependency.source and NBN_ResultValidator.source are
  composed on that SAME full result in NBX_ResultComposition.result_model
  and continuation. NBU's CLOSED-CONDITIONAL U03 afterstate/U04 lane children
  retain their original canonical domains and caller guard proofs.

L113: exit0,4.755490930s,peakRSS5,415,156KiB,swap0; both new roots standard
axioms only. The afterstate child’s successful bytes are discarded by this
parent (`?; Ok(())`), so the native control’s fixed success-byte payload adds
no successful-child or byte-value premise to the composition.

This promotion does not close ASR8 encoding, against-statement comparison,
emission or op53’s required frame instance. Those whole-member/native effect
rows remain as listed. The body-fidelity part of op53 remains out of soundness
scope under ruling(s); its actual call-site/frame obligation remains OPEN.
