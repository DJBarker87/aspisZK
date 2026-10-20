import CuSavingsCanonicalTail
import CuSavingsCanonicalInputHandback
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalVectorContexts
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsCanonicalDotsSources CuSavingsCanonicalVectorLoop
variable [Shared] [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]

theorem six_point_claim_context {O : Type}
    (ctx : (Usize→Result (core.result.Result field.wide_exact.WideExact AspisR1CanonicalDots.Error))→O)
    (scalarAt : Usize→VectorCommon)
    (base : I) (hb : SourceValue base) (powers : Array I 29#usize)
    (hp : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok powers) :
    ctx (fun point=>@new_callers.claim_dot _ (scalarAt point) (dotTable powers)) =
      ctx (fun point=>@old_callers.claim_dot _ (scalarAt point) (dotTable powers)) := by
  apply congrArg ctx
  funext point
  letI := scalarAt point
  exact claim_from_powers base hb powers hp

theorem four_slot_tail_context [VectorCommon] {O : Type}
    (ctx : (Usize→Result field.wide_exact.WideExact)→O)
    (bytes : Slice U8) (base : I) (hb : SourceValue base) (powers : Array I 29#usize)
    (hp : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok powers) :
    ctx (fun slot=>new_callers.tail bytes (dotTable powers) slot) =
      ctx (fun slot=>old_callers.tail bytes (dotTable powers) slot) := by
  apply congrArg ctx
  funext slot
  exact CuSavingsCanonicalTail.from_powers bytes slot base hb powers hp

#print axioms six_point_claim_context
#print axioms four_slot_tail_context
end AspisR1.CuSavingsCanonicalVectorContexts
