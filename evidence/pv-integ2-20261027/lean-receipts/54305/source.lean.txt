import PV_L2B_Rejection
import PV_L2B_Cursor
import PV_L2B_EntropyTrace
import PV_L2B_Guards
set_option autoImplicit false
namespace PV_L2B_JointTransport
theorem rejection_cursor_joint {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (PV_L2B_Rejection.trace n (xs.map (Option.map f)),
      PV_L2B_Cursor.offset (PV_L2B_Rejection.scan n (xs.map (Option.map f))).1) =
    (PV_L2B_Rejection.trace n xs, PV_L2B_Cursor.offset (PV_L2B_Rejection.scan n xs).1) := by
  rw [PV_L2B_Rejection.trace_relabel,PV_L2B_Rejection.count_map]
theorem accepted_conditional_uniform (q u p : ℚ) (n : Nat)
    (hp : p≠0) (h : u*p=1-q) (hs : PV_L2B_SamplerLaw.success q n≠0) :
    PV_L2B_SamplerLaw.valueMass q u n / PV_L2B_SamplerLaw.success q n = 1/p := by
  rw [PV_L2B_SamplerLaw.uniform_on_success q u p n hp h]
  field_simp
theorem constant_guard_joint {View Trace : Type} (v w : View) (tv tw : Trace)
    (hv : v=w) (ht : tv=tw) (checks : Nat) :
    (v,tv,PV_L2B_Guards.firstFailure (List.replicate checks false)) = (w,tw,checks) := by
  rw [hv,ht,PV_L2B_Guards.passing_trace]
#print axioms rejection_cursor_joint
#print axioms accepted_conditional_uniform
#print axioms constant_guard_joint
theorem outside_existing_event {I O : Type} (real sim : I → O) (bad : I → Prop)
    (agreement : ∀ i, ¬ bad i → real i=sim i) (i : I) :
    real i ≠ sim i → bad i := by
  intro h; by_contra hb; exact h (agreement i hb)
#print axioms outside_existing_event
theorem weighted_joint_transport {I O : Type} [Fintype I]
    (weight : I → ℚ) (real sim : I → O) (test : O → ℚ)
    (same : ∀ i, real i=sim i) :
    (∑ i : I, weight i*test (real i)) = ∑ i : I, weight i*test (sim i) := by
  apply Finset.sum_congr rfl
  intro i hi; rw [same i]
#print axioms weighted_joint_transport
end PV_L2B_JointTransport
