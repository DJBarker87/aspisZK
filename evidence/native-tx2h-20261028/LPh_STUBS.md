# NBQ substitutions and domains

No stub removes a headline premise. Native routing checks are separated from
callee value proofs; K-1 credit remains conditional where a reached copy matters.

| Native substitution | Named Lean result | Domain and credit |
|---|---|---|
| NBQ_public::push_route for canonical::Dot::push (K010/K015) | AspisR1.LPm_PublicState.private_source; AspisR1.LPi_RawValues.source | Two private canonical Q inputs; arbitrary four-u64 state. Stub havocs all four state words (overapproximation), checks full operands and K015 checks exact mutable receiver pointer/order. No arithmetic property is asserted from the havoc. Exact raw values and updates come from the CLOSED private-push bridge and these Lean roots. Canonical operands derived by LPi_CheckedInputs.canonical/from_wide/checked and NBQ_U06.push. |
| NBQ_public::no_push (K011/K012) | NBQ_U06.limit; NBQ_QChecks.push_invalid | Rejecting count or noncanonical scalar. Stub asserts false, so a pass proves it is unreachable, never a child success substitution. Whole state preserved in the Lean Result. |
| NBQ_error_control::private_format (K016) | NBQ_ErrorControl.rejects/frame; NBG_Error.transition | Pure private formatting erased under 03:00 scope; no claim about String bytes/length. This is an observation abstraction, not an exact-value field stub. Real formatting/std allocation and private cleanup remain the pinned standard/runtime boundary. |
| NBQ_error_control::private_log (K016) | NBQ_ErrorControl.frame | Returning log has no account-data writes under existing runtime log frame; one call, then InvalidInstructionData. Runtime effects/value are not supplied by Kani. |
| NBQ_powers::NBQ_emul::replacement for WideExact::mul (U07) | AspisR1.LPi_TowerValues.wide_mul; AspisR1.LPm_StubBounds.product/canonical_sum/residue | Both eight-word operands canonical. Exact inherited natural tower spec, any canonical output constrained to spec; natural word range makes wrapping reference operations exact. No native field multiplication is executed. Caller derives canonical inputs through powers induction. |
| NBQ_dots::child for four_dots_one (U07) | NONE: OPEN child bridge | Routing-only experiment. Never credit as four_dots_one closure or universal exact-value substitution. Parent must wait for complete child association. |
