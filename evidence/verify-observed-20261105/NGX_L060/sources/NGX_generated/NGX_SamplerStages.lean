import NGX_SamplerJoin
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SamplerStages
/-- The actual cohort pass is nominally the same emitted index program,
including failure and divergence. Native K021/K037 establish its cell/control
relation; pass_join performs the induction at remainder<P. -/
theorem pass_emitted (rank : Array U32 8#usize) :
 AspisR1PublicPreparation.sampler.qm31_div_pass rank=
 AspisR1Qm31SamplerIndex.sampler.qm31_div_pass rank := SamplerTransport.div_pass_eq rank

theorem digits_emitted (block : Array U8 32#usize) :
 AspisR1PublicPreparation.sampler.qm31_digits block=
 AspisR1Qm31SamplerIndex.sampler.qm31_digits block := SamplerTransport.digits_eq block

/-- Each arbitrary native high-to-low cell uses the same local division
relation; no whole pass/sampler equality is a hypothesis. -/
theorem pass_induction {r out : UInt64} {xs qs : List UInt32}
 (trace : LPk_Induction.Pass r xs out qs) (bound : r.toNat<SamplerMachineBounds.P) :
 (out,qs)=SamplerWordPass.machineProcess r xs := LPk_Induction.pass_join trace bound

theorem digits_induction {n : Nat} {xs out : List UInt32} {ds : List Nat}
 (trace : LPk_Induction.Digits n xs ds out) :
 (ds,out)=SamplerRepeatedPass.run n xs := LPk_Induction.digits_join trace

/-- The four native returned coordinates identify the whole emitted Result
at the same block, using the existing four-pass/packing association. -/
theorem sample {block : Array U8 32#usize} {q : aspis_core.field.QM31}
 (trace : NGT_Reduction.K block q) :
 AspisR1PublicPreparation.sampler.qm31_sample block=ok q := NGT_Reduction.scalar_k trace
#print axioms pass_emitted
#print axioms digits_emitted
#print axioms pass_induction
#print axioms digits_induction
#print axioms sample
end AspisR1.NGX_SamplerStages
