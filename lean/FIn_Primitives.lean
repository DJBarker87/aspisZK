import SAG_DotClosed
import SAG_FieldRead
import SAG_StageScale
import SAQ_RawWide
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Primitives
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

def field (bytes : Slice U8) (i : Usize) : Result E := do
  let x ← AspisR1CurrentWide.Proof.finishField bytes i
  ok (SAG_DotAdapter.toStageE x)

def add (x y : E) : Result E := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add
    (SAQ_WideABI.toW x) (SAQ_WideABI.toW y)
  ok (SAQ_WideABI.fromW z)

theorem add_value (x y z : E) (run : add x y = ok z) :
    CheckpointBytes5Output.ofE z = CheckpointBytes5Output.ofE x + CheckpointBytes5Output.ofE y := by
  unfold add at run
  obtain ⟨out,actual,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj rest
  rw [←same,SAG_StageScale.from_decode,SAQ_WideABI.w_decode,SAQ_WideABI.w_decode]
  exact SAQ_RawWide.add_exact _ _ _ actual

theorem field_value (bytes : Slice U8) (i : Usize) (x : E)
    (run : field bytes i = ok x) :
    FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice
      (MultiproofConeCanonical.bytesOf bytes.val) (32*i.val) 32) =
      some (CheckpointBytes5Output.ofE x) := by
  unfold field at run
  obtain ⟨out,actual,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj rest
  rw [←same,SAG_DotDecode.e_decode]
  change _ = some (AspisR1CurrentWide.Proof.decodeFinish
    (SAG_DotAdapter.toFinishE (SAG_DotAdapter.toStageE out)))
  rw [SAG_DotAdapter.roundtrip_finishE]
  exact SAG_FieldRead.from_finish bytes i out actual

#print axioms add_value
#print axioms field_value
end AspisR1.FIn_Primitives
end
