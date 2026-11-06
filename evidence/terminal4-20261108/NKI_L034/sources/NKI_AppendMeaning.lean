import NKI_AppendPacket
import NJB_PackLinearity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_AppendMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeValue (decode K)
def channel (j : Fin 4) : Bool := decide (j.val<2)
def group (j : Fin 4) : Fin 2 := ⟨j.val%2,Nat.mod_lt _ (by decide)⟩
def residual {index level frontier o high} (p : NKI_AppendPacket.Packet index level frontier o high) (i : Fin 8) : K :=
 decode high*(decode (NKI_DigestView.opened o (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)) (NKI_AppendPacket.start_bound _) i)-((NKI_DigestTargets.cells p.targets i).val : K))
def contribution {index level frontier o high} (p : NKI_AppendPacket.Packet index level frontier o high) (j : Fin 4) (k : Fin 4) : K :=
 if NKI_AppendPacket.emptySide index level=channel j then residual p (NJX_DigestGroups.index (group j) k) else 0
/-- Exact decoded association to packing the old8lane residual contribution,
with separate zero-bit/local0 and occupied/local12 channels. -/
theorem source {index level frontier o high} (p : NKI_AppendPacket.Packet index level frontier o high) (j : Fin 4) :
 decode (NKI_AppendPacket.output p j)=NJB_PackLinearity.pack (contribution p j) := by
 have v:=p.arithmetic.out_value
 cases side : NKI_AppendPacket.emptySide index level <;> fin_cases j <;>
  simp [NKI_AppendPacket.output,NKI_AppendPacket.carrier,contribution,channel,group,residual,side,
   FIv_NativeValue.zero.2,NJB_PackLinearity.zero,NJB_PackLinearity.scale,v]
#print axioms source
end AspisR1.NKI_AppendMeaning
end
