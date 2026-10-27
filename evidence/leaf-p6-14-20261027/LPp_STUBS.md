# LPp contextual substitutions and value pairings

No field operation is proved in Kani in this job. No new arithmetic stub is
needed: the closure gates abstract the already translated children by arbitrary
TYPED outcomes. All payload words range over u32; these CONTROL gates require
no canonicality restriction. Each child is called once. Assigning the ghost
outcomes to the actual child's result specializes the universal context gate;
the ghosts are not a proposed implementation of the arithmetic child.

| Context replacement | Paired Lean statement / domain |
|---|---|
| sampler LPp_sample + LPp_mapper | LPp.Total.mapper_law and circle_sample_exact, LPp.Closure.sampler_domain; every 32-byte block; actual canonicality derived from sample_total. LPp_sample chooses zero only to erase the child in the context gate; all mapper Result/error/payload outcomes are universally quantified independently. It is not a sampler-equivalence claim. |
| sampler LPp_fallback | LPp.Closure.capture, native_step; arbitrary row and both errors. Arbitrary fallback payload includes the concrete value established by LPp.Fallback.fallback0/1. Assertions establish the exact captured row index and exactly one invocation on Err, zero on Ok. |
| transcript LPp_draw + LPp_mapper | Generic typed Result continuation, all usize samples and both draw outcomes; arbitrary initial and post-draw state in passing K007 (169 checks). The native continuation preserves that entire post-draw state by arbitrary-coordinate checking. Actual draw body remains translated; no draw distribution or oracle-trace theorem is supplied by the context check. |
| transcript LPp_fallback | LPp.Closure.capture paired with the identical unwrap_or_else law, and fixed_fallback K005. Full usize capture is asserted before modulo, including draw-error short circuit. |
| LPp_fixed_mapper | LPp.MapperValues.mapper0/mapper1, native0_port/native1_port. Domain exactly t=(0,1) or (1,1) as two CM31 components. The stub ASSERTS that domain; K005 proves the actual array/modulo selection establishes it for every usize sample. Both return Ok with exact natural u32 limbs. defensive0_unreachable/defensive1_unreachable exclude the inner defensive error arm. |

R72 inverse pairing: LPp.inverse_nonzero/zero consume
SamplerClosureCircleFieldExecution.try_inverse_nonzero/zero, with cm_inv and
SamplerClosureCircleScalarTransport.inv_encode underneath. The squaring loop
and addition chain are reused symbolically. Inherited translated product value
ports are LPh.Native.m31_value, cm_mul_expanded, qm_mul_expanded,
qm_scalar_value, by_r_expanded, wide_mul_expanded (LPh_STUBS.md), and
LPf_BaseMultiply.source; their field/probe association is retained, not rerun.
They are not Kani multiplier proofs. No XRk/XRn qpow is imported or used.
