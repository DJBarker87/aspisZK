import NLL_ParentInvocation
set_option autoImplicit false
noncomputable section
namespace NLL_ParentSource
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (roots : Roots) (batch : Usize) :
 NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof raw roots batch ()=model H proof raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV := by
 have h0:=Port3_NativeBatchCalls.root_read roots 0
 have h1:=Port3_NativeBatchCalls.root_read roots 1
 have h2:=Port3_NativeBatchCalls.root_read roots 2
 unfold NKV_FRef.verifier.candidate.batch_merkle_values
 simp only [h0,h1,h2,bind_tc_ok]
 change NKV_ParentSource.three
   (fun i v => NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof raw (Port3_NativeBatchCalls.rootAt roots 0) batch 0#usize i v ())
   (fun i v => NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof raw (Port3_NativeBatchCalls.rootAt roots 1) batch 1#usize i v ())
   (fun i v => NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof raw (Port3_NativeBatchCalls.rootAt roots 2) batch 2#usize i v ())=_
 rw [NKV_ParentSource.three_next]
 rfl

set_option pp.proofs false
#print source
#print axioms source
end NLL_ParentSource
end
