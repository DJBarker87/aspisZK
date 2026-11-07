import NLV_RunLaws
import RPz7_SdkD_PrepareLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_LowerTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
def event : PreparedHashCode.Event → SdkC_Source.Parts × Result SdkC_Source.Digest
 | .digest _ _ parts reply => (parts,reply)
/-- Typed preparation events and SDK events are the SAME ordered attempted
parts/replies. Fail/div retain their terminal event and have no suffix. -/
theorem source {A : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (c : PreparedHashCode.Code A) (associated : SdkD_PrepareLower.Associated h c)
 (before : SdkC_Source.Log) :
 SdkC_Source.run h (SdkD_PrepareLower.lower c) before =
 ((PreparedHashCode.run c).2,before++(PreparedHashCode.run c).1.map event) := by
 induction c generalizing before with
 | done a => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,PreparedHashCode.run,List.map_nil,List.append_nil]
 | step r k ih =>
   cases r with
   | ok a => exact ih a associated before
   | fail e => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,PreparedHashCode.run,List.map_nil,List.append_nil]
   | div => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,PreparedHashCode.run,List.map_nil,List.append_nil]
 | digest D hash parts k ih =>
   have same := associated.1
   cases edge : h parts with
   | ok a =>
     have typed : D.digest hash parts=ok a := same.trans edge
     simp only [SdkD_PrepareLower.lower,SdkC_Source.run,edge,PreparedHashCode.run,typed]
     rw [ih a (associated.2 a)]
     simp only [List.map_cons,event,List.append_assoc,List.singleton_append]
   | fail e => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,edge,PreparedHashCode.run,same,edge,List.map_cons,List.map_nil,event,List.append_nil]
   | div => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,edge,PreparedHashCode.run,same,edge,List.map_cons,List.map_nil,event,List.append_nil]
#print axioms source
end AspisR1.NLV_LowerTrace
end
