import NKI_LevelsCohort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsComplete
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NJX_DigestCohort (O dc)
open NJX_AppendDomains (Frontier High)
open NJX_AppendFold (State)
/-- Full235 root, retaining child/native frame certificates and giving the
packed full-old-lane-sum cohort equality, not only intermediate sum values. -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (hf : ∀ d∈f.val,dc d) (ho : FIw_ArrayValue.canonical o) (hs : FIw_ArrayValue.canonical s) :
 ∃ (packets : NKI_LevelsChildren.Family index f o s) (out : State),
 (∀ i,NKI_LevelsFrame.call index f o s i=ok (NKI_AppendPacket.output (packets i)) ∧
  (∀ j,Canon (NKI_AppendPacket.output (packets i) j)) ∧ NKI_AppendCertificate.Native (packets i)) ∧
 NKI_LevelsFrame.run index f o s (List.finRange 20) NKI_LevelsRoot.zero=ok out ∧
 NKI_LevelsNative.Trace index f o s (fun i=>NKI_AppendPacket.output (packets i)) (List.finRange 20) NKI_LevelsRoot.zero out ∧
 (∀ j,Canon (out j)) ∧ ∀ j,decode (out j)=NKI_LevelsCohort.model index f o s packets j := by
 obtain ⟨packets,out,children,run,tr,ho,values⟩ := NKI_LevelsRoot.source index f o s hf ho hs
 exact ⟨packets,out,children,run,tr,ho,NKI_LevelsCohort.association index f o s packets out values⟩
#print source
#print axioms source
end AspisR1.NKI_LevelsComplete
end
