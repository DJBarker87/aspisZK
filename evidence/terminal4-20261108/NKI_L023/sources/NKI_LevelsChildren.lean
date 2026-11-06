import NKI_AppendCertificate
import NKI_LevelsFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsChildren
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O dc)
open NJX_AppendDomains (Frontier High)
abbrev Family (index : U64) (f : Frontier) (o : O) (s : High) :=
 (i : Fin 20) → NKI_AppendPacket.Packet index (NJX_AppendDomains.level i) (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i)
/-- Concrete234 at every actual frontier[level], high[34+level], SAME
index/openings. Every child domain and complete native/cohort clause is
produced here, not retained as a235 root hypothesis. -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (hf : ∀ d∈f.val,dc d) (ho : FIw_ArrayValue.canonical o) (hs : FIw_ArrayValue.canonical s) :
 ∃ packets : Family index f o s,∀ i,
 NKI_LevelsFrame.call index f o s i=ok (NKI_AppendPacket.output (packets i)) ∧
 (∀ j,Canon (NKI_AppendPacket.output (packets i) j)) ∧ NKI_AppendCertificate.Native (packets i) := by
 have children : ∀ i : Fin 20,∃ p : NKI_AppendPacket.Packet index (NJX_AppendDomains.level i) (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i),
  NKI_LevelsFrame.call index f o s i=ok (NKI_AppendPacket.output p) ∧
  (∀ j,Canon (NKI_AppendPacket.output p j)) ∧ NKI_AppendCertificate.Native p := by
  intro i
  have domains:=NJX_AppendDomains.source f s hs hf i
  exact NKI_AppendCertificate.source index _ _ o _ domains.2.1 domains.2.2.1 ho domains.1
 choose packets calls canonical native using children
 exact ⟨packets,fun i=>⟨calls i,canonical i,native i⟩⟩
#print source
#print axioms source
end AspisR1.NKI_LevelsChildren
end
