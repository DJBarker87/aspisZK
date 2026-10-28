import PV_B3_EvalRank222
import PV_B3_BoundedLoop
namespace PV_B3_WeightFinite222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Q × Usize

def body (point : Array Q 10#usize) (prefix_len prefixIndex : Usize) (s : State) :=
  host_multilinear.sparse_eq_weights_loop2_loop0.body point prefix_len prefixIndex s.1 s.2

theorem counter (point : Array Q 10#usize) (bound prefixIndex : Usize)
    (weight : Q) (i : Usize) (next : State)
    (h : body point bound prefixIndex (weight,i) = ok (cont next)) :
    i.val < bound.val ∧ next.2 = Usize.wrapping_add i 1#usize := by
  unfold body host_multilinear.sparse_eq_weights_loop2_loop0.body at h
  simp only [lift, bind_tc_ok] at h
  split at h
  · rename_i hi
    obtain ⟨q, _, h⟩ := bind_success _ _ _ h
    obtain ⟨product, _, h⟩ := bind_success _ _ _ h
    cases h
    exact ⟨hi, rfl⟩
  · cases h

def rank (bound : Usize) (s : State) : Nat := bound.val-s.2.val

theorem decreases (point : Array Q 10#usize) (bound prefixIndex : Usize) (s next : State)
    (h : body point bound prefixIndex s = ok (cont next)) : rank bound next < rank bound s := by
  rcases s with ⟨weight,i⟩
  obtain ⟨hi, hn⟩ := counter point bound prefixIndex weight i next h
  unfold rank
  dsimp only
  rw [hn, PV_B3_EvalRank222.increment i bound hi]
  omega

theorem source (point : Array Q 10#usize) (bound prefixIndex : Usize) (weight : Q) (i : Usize) :
    host_multilinear.sparse_eq_weights_loop2_loop0 point bound prefixIndex weight i =
      PV_B3_BoundedLoop.bounded (body point bound prefixIndex) (bound.val-i.val) (weight,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body point bound prefixIndex) (rank bound)
    (decreases point bound prefixIndex) _ _ (Nat.le_refl _)

#print axioms body
#print axioms counter
#print axioms rank
#print axioms decreases
#print axioms source
end PV_B3_WeightFinite222
