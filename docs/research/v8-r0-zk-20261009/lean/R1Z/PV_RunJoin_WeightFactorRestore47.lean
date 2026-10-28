import R1Z.PV_RunJoin_WeightFactorWrite47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightFactorRestore47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightFactorWrite47
open PV_B2_C_ConstructorRows (Factors)

theorem list_restore {A : Type} (xs : List A) (i : Nat) (x : A)
    (h : xs[i]?=some x) : xs.set i x=xs := by
  induction xs generalizing i with
  | nil => simp only [List.getElem?_nil] at h;cases h
  | cons a xs ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at h;subst a;rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set,ih i h]
#print axioms list_restore

theorem read_value {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i=ok x) : a.val[i.val]?=some x := by
  unfold Array.index_usize at h
  split at h
  · cases h
  · rename_i v hv
    cases Result.ok.inj h
    exact hv
#print axioms read_value

theorem complete (fs : Factors) (slot : Usize) (m : Matrix)
    (h : Array.index_usize fs slot=ok m) : Aeneas.Std.Array.set fs slot m=fs := by
  apply Subtype.ext
  change fs.val.set slot.val m=fs.val
  exact list_restore _ _ _ (read_value fs slot m h)
#print axioms complete
end R1Z.PV_RunJoin_WeightFactorRestore47
