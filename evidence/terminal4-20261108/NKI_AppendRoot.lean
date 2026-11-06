import NKI_AppendPacket
import NKI_TargetAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_AppendRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D dc)
/-- TX1:234 complete returning carrier. The actual right/occupied branch,
empty-root/last-word tweak, SAME prepared cache and every arithmetic child
are derived internally. Cut is the reviewed universal native relation;
its logged replies are instantiated from this ONE packet under (aq)(5). -/
theorem source (index : U64) (level : Usize) (frontier : D) (o : O) (high : NQ)
 (hl : level.val<20) (hf : dc frontier) (ho : FIw_ArrayValue.canonical o) (hh : Canon high) :
 ∃ p : NKI_AppendPacket.Packet index level frontier o high,
 NKI_AppendPacket.cohort index level frontier o high=ok (NKI_AppendPacket.output p) ∧
 (∀ j,Canon (NKI_AppendPacket.output p j)) ∧
 NKI_AppendCut.Cut (NKI_AppendPacket.emptySide index level) level high
  (NKI_DigestView.opened o (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)) (NKI_AppendPacket.start_bound _))
  (NJX_DigestCohort.dcells p.expected) p.targets.last
  p.arithmetic.prepared p.arithmetic.residual p.arithmetic.packed p.arithmetic.out (NKI_AppendPacket.output p)
  (NKI_AppendCut.observations level high
   (NKI_DigestView.opened o (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)) (NKI_AppendPacket.start_bound _)) (NJX_DigestCohort.dcells p.expected)
   p.targets.last (NKI_AppendPacket.emptySide index level) p.arithmetic.prepared p.arithmetic.residual p.arithmetic.packed)
  (if NKI_AppendPacket.emptySide index level then 23 else 21) ∧
 NKI_DigestTargets.cells p.targets=NKI_AppendCut.targets (NKI_AppendPacket.emptySide index level) (NJX_DigestCohort.dcells p.expected) p.targets.last := by
 obtain ⟨p,cp⟩ := NKI_AppendPacket.source index level frontier o high hl hf ho hh
 exact ⟨p,cp,NKI_AppendPacket.canonical p,NKI_AppendCut.source _ _ _ _ _ _ _ _ _ _,NKI_TargetAssociation.source p.targets⟩
#print source
#print axioms source
end AspisR1.NKI_AppendRoot
end
