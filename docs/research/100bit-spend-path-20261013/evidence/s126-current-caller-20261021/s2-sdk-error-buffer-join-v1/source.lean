import S2SdkErrorBufferFrameV1
import S2SdkProofGateJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ErrorBufferJoin
open BorrowedBufferFrame

/-- Complete borrowed-reference error execution supplies its own all-buffer
frame. No separate acquire/release, byte/frame or child-success premise. -/
theorem borrowed_error_buffers (ops : Ops) (program : Array U8 32#usize)
    (sdk out : OwnedSdk) (data : alloc.vec.Vec U8)
    (error : solana_program_error.ProgramError)
    (h : BorrowedReference.owned_stage1 ops program sdk data=ok (.Err error,out)) :
    buffers out=buffers sdk := by
  rw [BorrowedEquivalence.stage1_eq] at h
  exact ErrorBufferFrame.stage1_error_buffers ops program sdk out data error h

/-- The installed complete scalar-comparison/current-decoder caller retains
its complete public/proof/checkpoint buffers on every ordinary rejected run. -/
theorem installed_error_buffers (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk out : OwnedSdk) (data : alloc.vec.Vec U8)
    (error : solana_program_error.ProgramError)
    (h : ProofPrefixParent.stage1 ops verifierOps program sdk data=ok (.Err error,out)) :
    buffers out=buffers sdk := by
  rw [ProofGate.stage1_borrowed_eq] at h
  exact borrowed_error_buffers (Installation.install ops verifierOps) program sdk out data error h

/-- Every selected byte-vector read, including invalid-slot failure, is
preserved by that same complete rejected execution. The query has no range
premise and may alias any of the three logical account slots. -/
theorem installed_error_read (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk out : OwnedSdk) (data : alloc.vec.Vec U8)
    (error : solana_program_error.ProgramError) (queried : Usize)
    (h : ProofPrefixParent.stage1 ops verifierOps program sdk data=ok (.Err error,out)) :
    readBytes out queried=readBytes sdk queried :=
  readBytes_eq sdk out queried (installed_error_buffers ops verifierOps program sdk out data error h)

#print axioms borrowed_error_buffers
#print axioms installed_error_buffers
#print axioms installed_error_read
end AspisS2OwnedStage1.SdkReference.ErrorBufferJoin
