import RPv_FIw_ScalarArithmetic
import RPv_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_DigestArithmetic
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

def run (old selector opened : NQ) (target : U32) : Result NQ := do
  let lifted ← pool_v1.pair_forest_semantic_terminal.lift_m31 target
  let difference ← field.QM31.sub opened lifted
  let scaled ← field.QM31.mul selector difference
  field.QM31.add old scaled

theorem value (old selector opened out : NQ) (target : U32)
    (ho : Canon old) (hs : Canon selector) (ha : Canon opened)
    (ht : target.val<FIw_ScalarArithmetic.P) (success : run old selector opened target=ok out) :
    Canon out ∧ decode out=decode old+decode selector*(decode opened-(target.val : K)) := by
  unfold run at success
  obtain ⟨lifted,hl,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨difference,hd,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨scaled,hm,success⟩ := FIv_Map.bind_success _ _ _ success
  have same := Result.ok.inj ((FIw_ScalarArithmetic.lift_run target).symm.trans hl)
  have vl := FIw_ScalarArithmetic.lift_value target ht
  rw [same] at vl
  have vd := FIv_SubMap.qm opened lifted difference ha vl.1 hd
  have vm := FIv_NativeValue.mul selector difference scaled hs vd.1 hm
  have va := FIv_NativeValue.add old scaled out ho vm.1 success
  refine ⟨va.1,?_⟩
  rw [va.2,vm.2,vd.2,vl.2]
#print axioms value
end AspisR1.FIy_DigestArithmetic
end
