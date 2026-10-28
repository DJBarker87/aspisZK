import PV_B3_EvalRank222
import PV_B3_BoundedLoop
namespace PV_B3_SuffixFinite222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Usize × Usize

def body (point : Array Q 10#usize) (s : State) :=
  host_multilinear.sparse_eq_weights_loop1.body point s.1 s.2

theorem counter (point : Array Q 10#usize) (suffix i : Usize) (next : State)
    (h : body point (suffix,i) = ok (cont next)) :
    i.val < 10 ∧ next.2 = Usize.wrapping_add i 1#usize := by
  unfold body host_multilinear.sparse_eq_weights_loop1.body at h
  simp only [lift, bind_tc_ok] at h
  split at h
  · rename_i hi
    obtain ⟨q, _, h⟩ := bind_success _ _ _ h
    obtain ⟨b, _, h⟩ := bind_success _ _ _ h
    cases h
    exact ⟨hi, rfl⟩
  · cases h

def rank (s : State) : Nat := 10-s.2.val

theorem decreases (point : Array Q 10#usize) (s next : State)
    (h : body point s = ok (cont next)) : rank next < rank s := by
  rcases s with ⟨suffix,i⟩
  obtain ⟨hi, hn⟩ := counter point suffix i next h
  unfold rank
  dsimp only
  rw [hn, PV_B3_EvalRank222.increment i 10#usize hi]
  omega

theorem source (point : Array Q 10#usize) (suffix i : Usize) :
    host_multilinear.sparse_eq_weights_loop1 point suffix i =
      PV_B3_BoundedLoop.bounded (body point) (10-i.val) (suffix,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body point) rank
    (decreases point) _ _ (Nat.le_refl _)

#print axioms body
#print axioms counter
#print axioms rank
#print axioms decreases
#print axioms source
end PV_B3_SuffixFinite222
