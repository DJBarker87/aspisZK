import NKV_TreeSource
import NJS_Keys
import NJS_Sort
import NJS_Slot
import NJS_BatchLeaf
import NJE_CountPacket
import NJV_TX2
set_option autoImplicit false
noncomputable section
namespace NKV_ConcreteChildren
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_TreeSource NKV_ReturnBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def toExtract {X : Type} (D : aspis_core.digest.Digest32 X) :
 NJS_Extract.aspis_core.digest.Digest32 X := ⟨D.coremarkerCopyInst,D.digest⟩

def count (arity : Port3_NativeBatchBody.multiproof.Arity) (indices : Slice U32) : Result (Option Usize) :=
 match arity with | .Two => NJE_CountPacket.source indices | .Eight => fail .panic

/-- The exact endpoint of the CLOSED TX2:093 packet, not a free verdict or
selected scratch seed. Its <=9216 caller domain remains to be discharged from
SAME produced scratch before this is a positive native parent root. -/
def verify (H : Bytes → AspisV8R19.SourceDuplexStep.State) {X : Type} (_D : aspis_core.digest.Digest32 X) (_hash : X)
 (arity : Port3_NativeBatchBody.multiproof.Arity) (root : Array U8 32#usize)
 (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) : Result (Bool × Indices × Values) :=
 match arity with
 | .Two =>
   let out := (eval H (NJV_TX2Returning.endpoint root nodes idx val n)).2
   ok (out.1,out.2.idx,out.2.val)
 | .Eight => fail .panic

/-- All operation slots fixed to actual CLOSED children or pinned library
semantics. This definition alone is not a callee-domain/native certificate. -/
def ops (H : Bytes → AspisV8R19.SourceDuplexStep.State) : Port3_NativeBatchBody.Ops where
 op0 := Port3_BatchStd.anyDefault
 op1 := Port3_BatchStd.okOr
 op2 := NJS_Extract.verifier.candidate.opening
 op3 := NJS_Extract.verifier.candidate.slot NGD_SlotRef.slot_offset
 op4 := NJS_Extract.verifier.candidate.batch_keys
 op5 := NJS_Extract.verifier.candidate.sort_batch_keys
 op6 := fun D hash tree view => NJS_Extract.verifier.candidate.batch_leaf
   (ok 113#u8) (ok 241#u8) NJS_BatchLeaf.privateLeaf (toExtract D) hash tree view
 op7 := Port3_BatchStd.sameLeaf
 op8 := Port3_BatchStd.sameIndex
 op9 := Array.index_usize
 op10 := verify H
 op11 := count
 op12 := ok (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
 op13 := ok 10#usize
 unwrap8 := Port3_BatchStd.unwrap8

theorem installed (H : Bytes → AspisV8R19.SourceDuplexStep.State) : Port3_BatchStd.install (ops H)=ops H := rfl

def digest (H : Bytes → AspisV8R19.SourceDuplexStep.State) : aspis_core.digest.Digest32 Unit :=
 NJS_BatchLeaf.modelDigest (NJS_RuntimeDigest.backend H)

/-- Concrete source observation, with no arbitrary Ops parameter. This is
still SUPPORT ONLY: no reviewed whole native invocation or trace installation
is asserted, and the own/callee domains still require explicit discharge. -/
theorem source (H : Bytes → AspisV8R19.SourceDuplexStep.State) (proof : Slice U8) (queries : Array U32 22#usize)
 (root : Array U8 32#usize) (batch tree : Usize) (bound : batch.val<2)
 (idx : Indices) (val : Values) :
 reject (Port3_NativeBatchBody.verifier.candidate.batch_tree (ops H)
   (digest H) proof queries root batch tree idx val ())=
 reject (NKV_FRef.verifier.candidate.batch_tree (ops H)
   (digest H) proof queries root batch tree idx val ()) := by
 simpa only [installed] using NKV_TreeSource.source (ops H) (digest H) ()
   proof queries root batch tree bound idx val

set_option pp.proofs false
#print source
#print axioms installed
#print axioms source
end NKV_ConcreteChildren
end
