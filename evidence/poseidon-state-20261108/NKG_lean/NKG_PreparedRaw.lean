import NKG_OracleChoices
import RPv_FJa_MapRelation
import RPv_FJh_MapCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_PreparedRaw
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FJh_Base (cell)
open NKG_OracleCuts (Three Prepared)
open NKG_InternalChoices (get get_ok)
open NKG_OracleChoices (zeroPrepared)
def model (w : Three) : Prepared :=
 ⟨List.ofFn (fun i : Fin (3#usize).val=>get (field.PreparedQm31Multiplier.new (cell w i)) zeroPrepared),by simp⟩
/-- Raw result identity for the pinned std map, on SAME constructor calls.
This supplies all nine cache words; validity alone is not used as identity. -/
theorem source (w : Three) (p : Prepared)
 (run : FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP) w field.PreparedQm31Multiplier.new=ok p) : p=model w := by
 unfold FIq_Native.core.array.Array.map at run
 have rel := FJa_MapRelation.value (BuiltinFnMut NQ NP)
   (fun x y=>field.PreparedQm31Multiplier.new x=ok y) w field.PreparedQm31Multiplier.new p (by
     intro x hx y last called
     change (do let z ← field.PreparedQm31Multiplier.new x
                ok (z,field.PreparedQm31Multiplier.new))=ok (y,last) at called
     obtain ⟨z,rz,called⟩ := FIv_Map.bind_success _ _ _ called
     obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj called)
     exact ⟨rz,rfl⟩) run
 apply Subtype.ext
 apply List.ext_getElem
 · rw [p.property,(model w).property]
 · intro j hj hk
   have h3 : j<(3#usize).val := by simpa only [p.property] using hj
   let i : Fin (3#usize).val := ⟨j,h3⟩
   have called : field.PreparedQm31Multiplier.new (cell w i)=ok (cell p i) :=
     FJh_MapCells.get rel j (by simpa only [w.property] using h3) hj
   simpa only [model,List.getElem_ofFn,cell,i] using (get_ok _ _ _ called).symm

def replies (w : Three) (theta : NQ) : Array NP 4#usize :=
 ⟨List.ofFn (fun j : Fin (4#usize).val=>if h:j.val<3 then
   get (field.PreparedQm31Multiplier.new (cell w ⟨j.val,h⟩)) zeroPrepared
   else get (field.PreparedQm31Multiplier.new theta) zeroPrepared),by simp⟩
/-- K032's returned caches are exactly its chosen complete constructor
replies. No prepared-validity or endpoint equality is assumed. -/
theorem native (w : Three) (theta : NQ) (args : Array NQ 4#usize)
 (p : Prepared) (block : NP) (calls : Nat)
 (cut : NKG_OracleCuts.Prepare w theta args (replies w theta) p block calls) :
 p=model w ∧ block=get (field.PreparedQm31Multiplier.new theta) zeroPrepared := by
 constructor
 · apply Subtype.ext
   apply List.ext_getElem
   · rw [p.property,(model w).property]
   · intro j hj hk
     have h3 : j<3 := by simpa [p.property] using hj
     have value := cut.weightsReply ⟨j,h3⟩
     simpa only [model,replies,cell,List.getElem_ofFn,dif_pos h3] using value
 · have value := cut.blockReply
   simpa only [replies,cell,List.getElem_ofFn,show ¬ (3<3) from Nat.lt_irrefl 3,↓reduceDIte] using value
#print source
#print axioms source
#print native
#print axioms native
end AspisR1.NKG_PreparedRaw
end
