import R1Z.PV_RDB2D_SparseWeights
set_option autoImplicit false
namespace R1Z.PV_OWNI_MapMLength
open Aeneas Aeneas.Std Result
/-- Successful monadic enumeration preserves count; failures/divergence are
not assumed away by a pure-list replacement. -/
theorem length {A B : Type} (f : A → Result B) (xs : List A) (ys : List B)
 (h:xs.mapM f=ok ys) : ys.length=xs.length := by
 induction xs generalizing ys with
 | nil =>
  have hh : ([] : List B)=ys := by injection h
  subst ys
  rfl
 | cons x xs ih =>
  cases hx:f x with
  | fail e => simp only [List.mapM_cons,hx,bind_tc_fail] at h; cases h
  | div => simp only [List.mapM_cons,hx,bind_tc_div] at h; cases h
  | ok y =>
   cases ht:xs.mapM f with
   | fail e => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_fail] at h; cases h
   | div => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_div] at h; cases h
   | ok tail =>
    have hh : y::tail=ys := by
     have eq:(ok (y::tail) : Result (List B))=ok ys := by
      simpa only [List.mapM_cons,hx,ht,bind_tc_ok] using h
     exact Result.ok.inj eq
    subst ys
    rw [List.length_cons,List.length_cons,ih tail ht]
#print axioms length
end R1Z.PV_OWNI_MapMLength
