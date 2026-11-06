import NKV_ParentTotal
set_option autoImplicit false
noncomputable section
namespace NKV_OuterTotal
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem bind_roots (ops : Port3_NativeBatchBody.Ops) {X : Type} (D : aspis_core.digest.Digest32 X)
 (hash : X) (proof : Slice U8) (p : verifier.Prepared) (folded root0 root1 : Array U8 32#usize)
 (batch : Usize) (read0 : Array.index_usize p.roots 0#usize=ok root0)
 (read1 : Array.index_usize p.roots 1#usize=ok root1) :
 NKV_FRef.verifier.candidate.batch_merkle ops D proof p folded batch hash=
 NKV_FRef.verifier.candidate.batch_merkle_values ops D proof p.queries
   (Array.make 3#usize [root0,root1,folded]) batch hash := by
 unfold NKV_FRef.verifier.candidate.batch_merkle
 rw [read0]
 simp only [bind_tc_ok]
 rw [read1]
 simp only [bind_tc_ok]

theorem batch (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (p : verifier.Prepared) (folded : Array U8 32#usize) (batch : Usize)
 (hb : batch.val<2) (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144) :
 ∃ r,NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof p folded batch ()=ok r := by
 obtain ⟨r0,read0⟩:=NKV_ParentTotal.read p.roots 0#usize (by scalar_tac)
 obtain ⟨r1,read1⟩:=NKV_ParentTotal.read p.roots 1#usize (by scalar_tac)
 obtain ⟨r,total⟩:=NKV_ParentTotal.values H proof len parsed wire p.queries (Array.make 3#usize [r0,r1,folded]) batch hb canonical
 refine ⟨r,?_⟩
 rw [bind_roots (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) () proof p folded r0 r1 batch read0 read1]
 exact total

set_option pp.proofs false
#print bind_roots
#print batch
#print axioms bind_roots
#print axioms batch
end NKV_OuterTotal
end
