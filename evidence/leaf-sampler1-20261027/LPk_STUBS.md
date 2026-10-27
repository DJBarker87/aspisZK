# LPk step stub pairing

| Native stub | Paired Lean theorem | Domain and conclusion |
|---|---|---|
| `LPk_step_relation` for `LPk_step` in reverse-writeback harness | `LPk_Cohort.step_result`, `LPk_Step.machine_step`, `LPk_Step.unique` | All u64 remainders < P, all u32 limbs. Cohort returns ok with the quotient written to the selected limb, q*P+r=rem*2^32+limb, r<P. Relation uniquely selects the model step; quotient fits u32. |

Reverse-writeback starts at remainder 0 and each stub result has r<P,
so its domain is established at every call. Constant q*P+r fits u64 because
q is u32 and r<P. `LPk_Step.step_join` and `LPk_Induction.pass_join` transport
the relation to the machine model, without a division-equivalence Kani goal.

The from_fn harness has no arithmetic stub: it checks the library traversal
with an arbitrary transition of the shared captured quotient at each callback.
It makes no assertion about arithmetic inside that transition. Its caller
arithmetic is supplied by the independently checked pass relation and Lean
induction. No field multiplication stub is used.

The native single-step gate is still required; a paired Lean theorem alone
does not verify the Rust step. See LPk_LEAF.md for final stage status.

The accepted split traversal gates are K012 (order) and K013 (writeback).
They use the same relation in u128, avoiding specification-only u64 overflow
checks. q is u32 and r<P; `LPk_Modular.no_wrap` shows q*P+r<2^64, hence the
wide relation is exactly the natural relation above. K006's combined harness
timed out and is excluded. No timeout was raised. The domain remains rem<P
and every u32 limb; no canonical-limb restriction was added.

K008 verifies the native uncast quotient is at most u32::MAX; K009 verifies
native remainder<P, so casting the quotient to u32 preserves its value.
The wrapping-reconstruction gate uses only these already checked facts as
assumptions. `LPk_Modular.lift_identity` supplies the no-wrap lift. Its success
is still required before the native step can be considered verified.

Final native step discharge: **K008 + K009 + K020**. K020 checks the identical
native dividend/division/remainder expressions, with the constant specification
product written `(q << 31) - q`. `LPk_Constant.product/shift_no_wrap/
subtract_no_wrap/relation` prove this is exactly q*P and lift the wrapping word
identity to `LPk_Step.Relation`. This replaces all failed multiplier shapes;
the partial projection gates are not used to claim the full relation.
`LPk_Casts.native_pack/native_cast/cohort_cast` give the bitwise-pack and
scalar ports. Quotient cast uses K008; digit cast uses K009 and P<B.
The paired cohort theorem remains `LPk_Cohort.step_result` on the full domain.
No stub pairing or native arithmetic obligation is left open for this leaf.
