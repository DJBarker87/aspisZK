import RPv_FIx_HighSumInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_RangeFold
open FIv_NativeValue (K)
open FIx_HighSumInner (Selectors model)

theorem value (s : Selectors) (n start : Nat) (acc : K) :
    model s n start acc =
      (List.ofFn (fun i : Fin n => FIv_NativeArray.value s.high (start+i.val))).foldl (·+·) acc := by
  induction n generalizing start acc with
  | zero => rfl
  | succ n ih =>
    rw [model,ih,List.ofFn_succ,List.foldl_cons]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    change start+1+i.val=start+(i.val+1)
    omega
#print axioms value
end AspisR1.FIz_RangeFold
end
