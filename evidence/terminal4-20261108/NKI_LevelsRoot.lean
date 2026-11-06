import NKI_LevelsChildren
import NKI_LevelsNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsRoot
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NJX_DigestCohort (O dc)
open NJX_AppendDomains (Frontier High)
open NJX_AppendFold (State)
def zero : State := fun _=>FIq_Native.field.QM31.ZERO
/-- TX1:235 concrete ZERO-initialized20level caller. SAME234 packet at every
actual argument, all4cells and all native step/frame packets in source order.
Only actual root-input canonicality; no child-success, output, Ops or Run
hypothesis. Credit still waits for the combined audit and next ledger. -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (hf : ∀ d∈f.val,dc d) (ho : FIw_ArrayValue.canonical o) (hs : FIw_ArrayValue.canonical s) :
 ∃ (packets : NKI_LevelsChildren.Family index f o s) (out : State),
 (∀ i,NKI_LevelsFrame.call index f o s i=ok (NKI_AppendPacket.output (packets i)) ∧
  (∀ j,Canon (NKI_AppendPacket.output (packets i) j)) ∧ NKI_AppendCertificate.Native (packets i)) ∧
 NKI_LevelsFrame.run index f o s (List.finRange 20) zero=ok out ∧
 NKI_LevelsNative.Trace index f o s (fun i=>NKI_AppendPacket.output (packets i)) (List.finRange 20) zero out ∧
 (∀ j,Canon (out j)) ∧ ∀ j,decode (out j)=((List.finRange 20).map (fun i=>decode (NKI_AppendPacket.output (packets i) j))).sum := by
 obtain ⟨packets,children⟩ := NKI_LevelsChildren.source index f o s hf ho hs
 let child := fun i=>NKI_AppendPacket.output (packets i)
 have calls : ∀ i,NKI_LevelsFrame.call index f o s i=ok (child i) := fun i=>(children i).1
 have hc : ∀ i j,Canon (child i j) := fun i=>(children i).2.1
 obtain ⟨out,co,tr,ho,vo⟩ := NJX_AppendFold.zero_source child hc
 refine ⟨packets,out,children,?_,NKI_LevelsNative.source index f o s child calls tr,ho,vo⟩
 rw [NKI_LevelsFrame.association index f o s child calls]
 exact co
#print source
#print axioms source
end AspisR1.NKI_LevelsRoot
end
