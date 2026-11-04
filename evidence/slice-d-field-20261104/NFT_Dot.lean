import RPv_FJh_M31DotSevenExact
import NFT_ChannelModel
set_option autoImplicit false
namespace NFT_Dot
open Aeneas Aeneas.Std Result

theorem scalar_product (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    ∃ p : U64, UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)=ok p ∧ p.val=a.val*b.val := by
  have widen (x : U32) : (UScalar.cast .U64 x).val=x.val := AspisR1.ExtractedMaskReducer.cast_widen_value x
  obtain ⟨p,run,value⟩:=AspisR1.ExtractedMaskReducerOps.mul_success
    (UScalar.cast .U64 a) (UScalar.cast .U64 b) (by
      rw [widen,widen]
      exact Nat.lt_trans (NFT_ChannelModel.product_bound a.val b.val ha hb) (by norm_num))
  exact ⟨p,run,by simpa only [widen] using value⟩

/-- Exact source index/term order for the adopted seven-term caller. -/
theorem control :
    ([0,4] : List Nat).flatMap (fun start => (List.range (min (start+4) 7-start)).map (fun j => (start,start+j)))=
      [(0,0),(0,1),(0,2),(0,3),(4,4),(4,5),(4,6)] := by rfl

#print axioms scalar_product
#print axioms control
end NFT_Dot
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s:=n.toString
  if (s.endsWith "source_success" && (s.splitOn "M31DotSevenExact").length>1) || (s.endsWith "loop_success_fuel" && (s.splitOn "M31DotChunkModel").length>1) then logInfo m!"COHERENT_ROOT {n}"
