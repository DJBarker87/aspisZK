import R1Z.PV_CB_ForwardLoop
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalForward
open Aeneas Aeneas.Std Result PV_CB_ForwardRange

theorem finite {A : Type} (predicate : A → Prop) (step : Usize → A → Result A)
    (stop : Usize)
    (preserve : ∀ i, i.val < stop.val → ∀ state, predicate state →
      ∃ out, step i state = ok out ∧ predicate out)
    (fuel : Nat) (i : Usize) (state : A) (rank : i.val + fuel = stop.val)
    (valid : predicate state) :
    ∃ out, PV_CB_ForwardLoop.finite step fuel i state = ok out ∧ predicate out := by
  induction fuel generalizing i state with
  | zero => exact ⟨state,rfl,valid⟩
  | succ fuel ih =>
    have inside : i.val < stop.val := by omega
    obtain ⟨next,hnext,vnext⟩ := preserve i inside state valid
    have next_rank : (advance i).val + fuel = stop.val := by
      rw [advance_val i stop inside]
      omega
    obtain ⟨out,hout,vout⟩ := ih (advance i) next next_rank vnext
    exact ⟨out,by simp only [PV_CB_ForwardLoop.finite,hnext,bind_tc_ok,hout],vout⟩
#print axioms finite
end R1Z.PV_CB_CanonicalForward
