import NDO_JGa_Map
import RPv_FIv_PreparedNewTotal
import RPv_FJh_PreparedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_PreparedMap
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
/-- Exact three-element std map of the actual constructor, including its
complete typed cache return; no arbitrary cache-validity hypothesis. -/
theorem result (w : Array NQ 3#usize) (cw : canonical w) :
 ∃ p,FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP) w field.PreparedQm31Multiplier.new=ok p := by
 obtain ⟨p,rp,_⟩ := JGa_Map.source (BuiltinFnMut NQ NP) (fun _=>True) w field.PreparedQm31Multiplier.new (by
   intro x hx
   obtain ⟨p,run,_⟩ := FIv_PreparedNewTotal.value x (cw x hx)
   refine ⟨p,?_,True.intro⟩
   change (do let y ← field.PreparedQm31Multiplier.new x
              ok (y,field.PreparedQm31Multiplier.new))=ok (p,field.PreparedQm31Multiplier.new)
   rw [run,bind_tc_ok])
 exact ⟨p,rp⟩
#print result
#print axioms result
end AspisR1.NKG_PreparedMap
end
