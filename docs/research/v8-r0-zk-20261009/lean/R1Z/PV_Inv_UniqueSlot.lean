import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup
set_option autoImplicit false
namespace R1Z.PV_Inv_UniqueSlot
variable {A I K : Type} [DecidableEq I] [AddCommMonoid K]

def selectedSum (xs : List A) (key : A → I) (value : A → K) (target : I) : K :=
  (xs.map (fun x => if key x=target then value x else 0)).sum

theorem selected_eq (xs : List A) (key : A → I) (value : A → K)
    (unique : (xs.map key).Nodup) (x : A) (member : x ∈ xs) :
    selectedSum xs key value (key x)=value x := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    have hnodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with he|ht
    · subst x
      have hzero : (ys.map (fun z => if key z=key y then value z else 0)).sum=0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hv
        have hn : key z ≠ key y := by
          intro hh
          exact hnodup.1 (List.mem_map.mpr ⟨z,hz,hh⟩)
        simp [hn]
      simp [selectedSum,hzero]
    · have hn : key y ≠ key x := by
        intro hh
        exact hnodup.1 (List.mem_map.mpr ⟨x,ht,hh.symm⟩)
      simpa [selectedSum,hn] using ih hnodup.2 ht

#print axioms selected_eq
end R1Z.PV_Inv_UniqueSlot
