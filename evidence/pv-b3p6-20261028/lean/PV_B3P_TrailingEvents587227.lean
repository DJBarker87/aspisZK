import PV_B3P_DominatedEvents578227
import PV_B3P_MaskIntrinsicSpec542227
namespace PV_B3P_TrailingEvents587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
open PV_B3P_MaskSource542227
set_option autoImplicit false
/-- Exact nonzero source loop test precedes the cttz wrapper. The source
U32-to-usize cast is retained, including its modular scalar semantics. -/
def sourceEvent (bits : BitVec 16) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  if bits ≠ 0 then
    let count : U32 := ⟨cttz16_spec542 bits⟩
    through effects (some ⟨(UScalar.cast .Usize count).val,16⟩)
  else .ok none

theorem event_guard (bits : BitVec 16) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent bits effects = .ok (some observed)) :
    indexGuard observed := by
  by_cases nonzero : bits ≠ 0
  · simp only [sourceEvent,if_pos nonzero] at ran
    have frame := through_value _ _ _ ran
    cases frame
    have bound := cttz16_nonzero_bound542 bits nonzero
    change (UScalar.cast .Usize (⟨cttz16_spec542 bits⟩ : U32)).val < 16
    rw [UScalar.cast_val_eq]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) bound
  · simp only [sourceEvent,if_neg nonzero] at ran
    cases ran

theorem event_certificate {α : Type} (bits : BitVec 16) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent bits effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard bits effects observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_TrailingEvents587227
