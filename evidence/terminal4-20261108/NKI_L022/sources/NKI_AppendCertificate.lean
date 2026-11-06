import NKI_AppendRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_AppendCertificate
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D dc)
def Native {index : U64} {level : Usize} {frontier : D} {o : O} {high : NQ}
 (p : NKI_AppendPacket.Packet index level frontier o high) : Prop :=
 NKI_AppendCut.Cut (NKI_AppendPacket.emptySide index level) level high
  (NKI_DigestView.opened o (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)) (NKI_AppendPacket.start_bound _))
  (NJX_DigestCohort.dcells p.expected) p.targets.last
  p.arithmetic.prepared p.arithmetic.residual p.arithmetic.packed p.arithmetic.out (NKI_AppendPacket.output p)
  (NKI_AppendCut.observations level high
   (NKI_DigestView.opened o (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)) (NKI_AppendPacket.start_bound _)) (NJX_DigestCohort.dcells p.expected)
   p.targets.last (NKI_AppendPacket.emptySide index level) p.arithmetic.prepared p.arithmetic.residual p.arithmetic.packed)
  (if NKI_AppendPacket.emptySide index level then 23 else 21) ∧
 NKI_DigestTargets.cells p.targets=NKI_AppendCut.targets (NKI_AppendPacket.emptySide index level) (NJX_DigestCohort.dcells p.expected) p.targets.last
theorem source (index : U64) (level : Usize) (frontier : D) (o : O) (high : NQ)
 (hl : level.val<20) (hf : dc frontier) (ho : FIw_ArrayValue.canonical o) (hh : Canon high) :
 ∃ p : NKI_AppendPacket.Packet index level frontier o high,
 NKI_AppendPacket.cohort index level frontier o high=ok (NKI_AppendPacket.output p) ∧
 (∀ j,Canon (NKI_AppendPacket.output p j)) ∧ Native p :=
 NKI_AppendRoot.source index level frontier o high hl hf ho hh
#print Native
#print axioms source
end AspisR1.NKI_AppendCertificate
end
