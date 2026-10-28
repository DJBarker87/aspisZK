import NCE_AdmissionCuts
import NCE_VerifierCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_VerifierAdmission
open Aeneas Aeneas.Std NCE_OpeningCuts NCE_AdmissionCuts NCE_VerifierCuts
open MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

/-- The actual carried index prefix has exactly the owned model's live keys. -/
theorem same_indices (s : Carrier) :
    cells (index s) 0 s.scratch.n.val =
      (MultiproofConePhysicalViews.live s.scratch 0 s.scratch.n.val).map Prod.fst := by
  simp only [cells,index,MultiproofConePhysicalViews.live,MultiproofConePhysicalLive.view,
    MultiproofConePhysicalViews.decodeEntry,MultiproofConePhysicalLive.cell,List.map_map,
    Function.comp_def]

def admitted (entry : Entry) (pair range : Predicate) (s : Carrier) (bytes : Nat) : Bool × Carrier :=
  if 16 < s.scratch.n.val then entry s bytes false else
    let out := check pair range s
    entry out.2 bytes out.1

/-- The entry Boolean is COMPUTED from one-window native predicates on the
SAME scratch, then supplied to the native source PC. No whole admission or
successful child return is introduced as a hypothesis. -/
theorem entry_model (entry : Entry) (exit : Exit) (finish : Finish)
    (control : NCE_Native_Verifier entry exit finish) (pair range : Predicate)
    (predicates : NCE_Native_Admission pair range) (s : Carrier) (bytes : Nat)
    (size : bytes ≤ 5504) :
    admitted entry pair range s bytes =
      (decide (OraclePortFrozenOrder.wellFormed
        ((MultiproofConePhysicalViews.live s.scratch 0 s.scratch.n.val).map Prod.fst) ∧ bytes%32=0),s) := by
  rw [←same_indices s]
  have length : (cells (index s) 0 s.scratch.n.val).length = s.scratch.n.val := by
    simp only [cells,List.length_map,List.length_range]
  by_cases big : 16 < s.scratch.n.val
  · have invalid : ¬ OraclePortFrozenOrder.wellFormed (cells (index s) 0 s.scratch.n.val) := by
      intro valid
      have bound := valid.2.1
      rw [length] at bound
      omega
    rw [admitted,if_pos big,NCE_VerifierCuts.rejected_entry entry exit finish control s bytes size]
    simp only [invalid,false_and,decide_false]
  · have small : s.scratch.n.val ≤ 16 := by omega
    rw [admitted,if_neg big,check_eq pair range predicates s small]
    simp only
    rw [control.1 s bytes _ size]
    by_cases well : OraclePortFrozenOrder.wellFormed (cells (index s) 0 s.scratch.n.val)
    · have truth := (NBI_Admission.admission_iff _).mpr well
      have positive : 0 < s.scratch.n.val := by
        by_contra zero
        have empty : cells (index s) 0 s.scratch.n.val = [] := by
          have zn : s.scratch.n.val = 0 := by omega
          simp only [zn,cells,List.range_zero,List.map_nil]
        exact well.1 empty
      simp only [truth,positive,small,well,true_and,Bool.and_true]
    · have reject : NBI_Admission.admission (cells (index s) 0 s.scratch.n.val) = false := by
        cases h : NBI_Admission.admission (cells (index s) 0 s.scratch.n.val) with
        | false => rfl
        | true => exact False.elim (well ((NBI_Admission.admission_iff _).mp h))
      simp only [reject,Bool.and_false,well,false_and,decide_false]

#print axioms same_indices
#print axioms entry_model
end AspisR1.NCE_VerifierAdmission
end
