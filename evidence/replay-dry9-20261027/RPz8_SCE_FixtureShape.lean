import RPz8_SCE_FixtureGame
import RPz8_SCE_FixtureAdmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureShape
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry SCE_FixtureData

theorem size_saved : saved.val.length = 1768 := by
  simp only [saved,Hist_Nonvacuity.checkpoint,List.length_cons,List.length_replicate]
theorem size_before : (e1.buffers 2).val.length = 1768 := by
  change (if (1 : Nat) = 0 then ([] : List U8) else (zeros 1768 (by decide)).val).length = 1768
  simp only [show (1 : Nat) ≠ 0 by decide,if_false,zeros,List.length_replicate]
theorem first_cell : (e1.handles 2).1 = 2 := rfl
theorem second_cell : (e2.handles 6).1 = 2 := rfl
theorem original_zero : Hir_ProvenanceModel.Zero (e1.buffers 2) := by
  change ∀ b ∈ (zeros 1768 (by decide)).val, b = 0#u8
  intro b member
  exact List.eq_of_mem_replicate member

theorem marker : Hist_Store.Initialized saved.deref := Hist_Nonvacuity.initialized

theorem nonalias_first (a : Nat) (small : a < 3) (other : a ≠ 2) :
    (e1.handles a).1 ≠ (e1.handles 2).1 := by
  change a ≠ 2
  exact other

theorem nonalias_second (a : Nat) (small : a < 7) (other : a ≠ 6) :
    (e2.handles a).1 ≠ (e2.handles 6).1 := by
  intro same
  exact other (SCE_FixtureAdmission.reader_injective a 6 small (by decide) same)

#print axioms size_saved
#print axioms size_before
#print axioms first_cell
#print axioms second_cell
#print axioms original_zero
#print axioms marker
#print axioms nonalias_first
#print axioms nonalias_second
end AspisR1.SCE_FixtureShape
end
