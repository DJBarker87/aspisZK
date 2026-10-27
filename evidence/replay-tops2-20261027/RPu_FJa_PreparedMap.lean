import RPu_FJa_MapRelation
import RPu_FIv_PreparedNewTotal
import RPu_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PreparedMap
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_PreparedNew (NP prepared)
/-- ORIGINAL prepared-weight map preserves ordered association to every SAME
input weight. Prepared multipliers are derived from actual new calls. -/
theorem value {N : Usize} (a : Array NQ N) (out : Array NP N)
    (hc : FIw_ArrayValue.canonical a)
    (run : FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP) a field.PreparedQm31Multiplier.new=ok out) :
    List.Forall₂ (fun x p=>ExtractedMaskPreparedState.PreparedFor (prepared p) (qm x)) a.val out.val := by
  unfold FIq_Native.core.array.Array.map at run
  apply FJa_MapRelation.value (BuiltinFnMut NQ NP) _ a field.PreparedQm31Multiplier.new out ?_ run
  intro x hx p last call
  change (do let p ← field.PreparedQm31Multiplier.new x;ok (p,field.PreparedQm31Multiplier.new))=ok (p,last) at call
  obtain ⟨p1,hp,call⟩ := FIv_Map.bind_success _ _ _ call
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj call)
  exact ⟨FIv_PreparedNew.valid x p1 (hc x hx) hp,rfl⟩
#print axioms value
end AspisR1.FJa_PreparedMap
end
