import PV_B1_HostSumOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostSumOption
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem none_iff (ops : ExternalFuns) (xs : Slice HQ) :
    (selected ops).op230 xs=ok none ↔ Slice.len xs≠1024#usize := by
  by_cases h : Slice.len xs=1024#usize
  · rw [PV_B1_HostSumOutcome.exact_length ops xs h]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact False.elim (impossible h)
  · rw [PV_B1_HostSumOutcome.wrong_length ops xs h]
    exact ⟨fun _ => h,fun _ => rfl⟩
theorem some_iff (ops : ExternalFuns) (xs : Slice HQ) (y : HQ) :
    (selected ops).op230 xs=ok (some y) ↔ Slice.len xs=1024#usize ∧
      xs.val.foldl PV_B1_HostSumValue.add PV_B1_HostSumValue.zero=y := by
  by_cases h : Slice.len xs=1024#usize
  · rw [PV_B1_HostSumOutcome.exact_length ops xs h]
    simp only [Result.ok.injEq,Option.some.injEq,h,true_and]
  · rw [PV_B1_HostSumOutcome.wrong_length ops xs h]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨impossible,_⟩; exact False.elim (h impossible)
#print axioms none_iff
#print axioms some_iff
end PV_B1_HostSumOption
