import PV_B3_EvalRank222
import PV_B3_BoundedLoop
namespace PV_B3_WeightsFinite222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev Data := Array (Usize × Q) 1024#usize
abbrev State := Data × Usize

def body (point : Array Q 10#usize) (prefix_len trailing_boolean suffix bound : Usize)
    (s : State) :=
  host_multilinear.sparse_eq_weights_loop2.body point prefix_len trailing_boolean suffix bound s.1 s.2

theorem counter (point : Array Q 10#usize) (prefix_len trailing_boolean suffix bound : Usize)
    (a : Data) (i : Usize) (next : State)
    (h : body point prefix_len trailing_boolean suffix bound (a,i) = ok (cont next)) :
    i.val < bound.val ∧ next.2 = Usize.wrapping_add i 1#usize := by
  unfold body host_multilinear.sparse_eq_weights_loop2.body at h
  simp only [lift, bind_tc_ok] at h
  split at h
  · rename_i hi
    obtain ⟨weight, _, h⟩ := bind_success _ _ _ h
    obtain ⟨a1, _, h⟩ := bind_success _ _ _ h
    cases h
    exact ⟨hi, rfl⟩
  · cases h

def rank (bound : Usize) (s : State) : Nat := bound.val-s.2.val

theorem decreases (point : Array Q 10#usize) (prefix_len trailing_boolean suffix bound : Usize)
    (s next : State) (h : body point prefix_len trailing_boolean suffix bound s = ok (cont next)) :
    rank bound next < rank bound s := by
  rcases s with ⟨a,i⟩
  obtain ⟨hi, hn⟩ := counter point prefix_len trailing_boolean suffix bound a i next h
  unfold rank
  dsimp only
  rw [hn, PV_B3_EvalRank222.increment i bound hi]
  omega

theorem source (point : Array Q 10#usize) (prefix_len trailing_boolean suffix bound : Usize)
    (a : Data) (i : Usize) :
    host_multilinear.sparse_eq_weights_loop2 point prefix_len trailing_boolean suffix a bound i =
      PV_B3_BoundedLoop.bounded (body point prefix_len trailing_boolean suffix bound)
        (bound.val-i.val) (a,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body point prefix_len trailing_boolean suffix bound)
    (rank bound) (decreases point prefix_len trailing_boolean suffix bound) _ _ (Nat.le_refl _)

#print axioms body
#print axioms counter
#print axioms rank
#print axioms decreases
#print axioms source
end PV_B3_WeightsFinite222
