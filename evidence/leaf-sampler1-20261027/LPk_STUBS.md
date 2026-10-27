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
