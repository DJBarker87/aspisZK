import R1Z.PV_RunJoin_QueryAccess64
import R1Z.PV_RunJoin_BackendMInput58
import R1Z.PV_RunJoin_SemanticEmbed50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryWordTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

def length : host_commitment.Word → Nat
  | .Base v => v.length
  | .Secure v => v.length

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (word : host_commitment.Word) (i : Usize)
    (bound : i.val<length word) :
    ∃ w, @host_commitment.Word.value (types base) (selected base heap box ops) word i=ok w := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  cases word with
  | Base v =>
    obtain ⟨m,hm⟩ := PV_RunJoin_QueryAccess64.vector v i bound
    refine ⟨PV_RunJoin_BackendMInput58.value m,?_⟩
    simp only [host_commitment.Word.value,hm,bind_tc_ok,PV_RunJoin_BackendMInput58.complete]
  | Secure v =>
    obtain ⟨q,hq⟩ := PV_RunJoin_QueryAccess64.vector v i bound
    obtain ⟨w,hw⟩ : ∃ w, aspis_core.field.wide_exact.WideExact.from_qm31 q=ok w := by
      exact ⟨_,PV_RunJoin_SemanticEmbed50.complete base heap box ops q⟩
    exact ⟨w,by simp only [host_commitment.Word.value,hq,bind_tc_ok,hw]⟩

#print axioms length
#print axioms complete
end R1Z.PV_RunJoin_QueryWordTotal64
