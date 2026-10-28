import R1Z.PV_RDB2D_SparseWeights
namespace R1Z.PV_RDB2D_SparseWeightsLength
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem mapM_length {A B : Type} (f : A → Result B) (xs : List A) (ys : List B)
    (h : xs.mapM f=ok ys) : ys.length=xs.length := by
  induction xs generalizing ys with
  | nil =>
    change ok []=ok ys at h
    cases h
    rfl
  | cons x xs ih =>
    cases hx : f x with
    | fail e => simp only [List.mapM_cons,hx,bind_tc_fail,reduceCtorEq] at h
    | div => simp only [List.mapM_cons,hx,bind_tc_div,reduceCtorEq] at h
    | ok y =>
      cases ht : xs.mapM f with
      | fail e => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_fail,reduceCtorEq] at h
      | div => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_div,reduceCtorEq] at h
      | ok tail =>
        have he0 : (ok (y::tail) : Result (List B))=ok ys := by
          simpa only [List.mapM_cons,hx,ht,bind_tc_ok] using h
        have he : y::tail=ys := Result.ok.inj he0
        subst ys
        simp only [List.length_cons,ih tail ht]

theorem exact_capacity {K : Type} (ops : PV_RDB2D_SparseWeights.WeightOps K)
    (point : List K) (width trailing suffix : Nat) (entries : List (Nat × K))
    (h : PV_RDB2D_SparseWeights.build ops point width trailing suffix=ok entries) :
    entries.length=2^width := by
  unfold PV_RDB2D_SparseWeights.build at h
  have hh := mapM_length _ (List.range (2^width)) entries h
  simpa only [List.length_range] using hh

#print axioms mapM_length
#print axioms exact_capacity
end R1Z.PV_RDB2D_SparseWeightsLength
