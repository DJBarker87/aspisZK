import Port8EFF_CheckpointCode
import Port1_Library

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_Bodies
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port6CK_Semantic (Unwrap)

/-- Current helper leaves, exact production checkpoint/proof/public/variant;
only the existing native error-carrier conversion follows the parent. -/
def readerCode (reserved : Bool) (unwrap : Unwrap) (ck proof pub : Slice U8)
    (v : transport.Variant) : CheckpointBytes5Effect.Code
      (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub v
  pure (match out with
    | .Ok pair => .Ok pair
    | .Err e => .Err (Port3_CheckpointInstall.error e))

def writerCode (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) :
    CheckpointBytes5Effect.Code (alloc.vec.Vec U8) := do
  let ck ← CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
    (CheckpointBytes3Namespaces.toAccumulator a) proof pub
  pure ⟨ck.val,ck.property⟩

def reader (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) :=
  Port8EFF_CheckpointCode.program (VTop_Checkpoint.digest D) hash (readerCode reserved unwrap ck proof pub v)

def writer {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : Hash) :=
  Port8EFF_CheckpointCode.program (VTop_Checkpoint.digest D) hash (writerCode p a proof pub)

/-- Full source return equality, including rejection and outer failure. The
lower bound comes from the installed size leaf, not a whole-op hypothesis. -/
theorem reader_value (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) (H : Bytes → State) :
    (eval H (reader reserved unwrap D ck proof pub v hash)).2 =
      Port6CK_Reader.reader reserved unwrap D ck proof pub v hash := by
  rw [reader,Port8EFF_CheckpointCode.value]
  simp only [readerCode,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure]
  rw [CheckpointBytes5Resume.source,← Port4A_ReaderNormalize.source
    (Port6CK_Ops.ops reserved unwrap) (Port6CK_Reader.size_bound reserved unwrap)]
  unfold Port6CK_Reader.reader
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out _
  cases out <;> rfl

theorem writer_value {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (hash : Hash) (H : Bytes → State) :
    (eval H (writer D p a proof pub hash)).2 = Port3_CheckpointInstall.writer D p a proof pub hash := by
  rw [writer,Port8EFF_CheckpointCode.value]
  simp only [writerCode,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure]
  rfl

/-- Every ordinary accepted OR rejected reader return carries the complete
current source-code log, not a selected successful model trace. -/
theorem reader_effects (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (out : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
    (actual : Port6CK_Reader.reader reserved unwrap D ck proof pub v hash=ok out) :
    ∃ after, CheckpointBytes5Effect.run (VTop_Checkpoint.digest D) hash
      (readerCode reserved unwrap ck proof pub v) []=ok (out,after) ∧
      eval H (reader reserved unwrap D ck proof pub v hash)=
        (CheckpointBytes5Inputs.observe after,ok out) := by
  have erased := (Port8EFF_CheckpointCode.value (VTop_Checkpoint.digest D) hash
    (readerCode reserved unwrap ck proof pub v) H).symm.trans
      ((reader_value reserved unwrap D ck proof pub v hash H).trans actual)
  obtain ⟨after,ran⟩ := Port3_CheckpointInstall.erase_success_run _ _ _ out erased []
  have pair := Port8EFF_CheckpointCode.effects _ _ _ H oracle out [] after ran
  exact ⟨after,ran,Prod.ext pair.1.symm pair.2⟩

/-- Only owned checkpoint bodies are replaced. All other thirteen-body
obligations retain the supplied implementation, including Session A op7. -/
def body (reserved : Bool) (unwrap : Unwrap) (other : VTop_OracleCode.Implementation) :
    VTop_OracleCode.Implementation := fun call => match call with
  | .op8 D p a proof pub hash => writer D p a proof pub hash
  | .op18 D ck proof pub v hash => reader reserved unwrap D ck proof pub v hash
  | call => other call

def implementation (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : VTop_OracleCode.Implementation) : VTop_OracleCode.Implementation :=
  Port1_Library.implementation ops (body reserved unwrap other)

theorem installed_reader (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : VTop_OracleCode.Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) :
    implementation ops reserved unwrap other (.op18 D ck proof pub v hash)=
      reader reserved unwrap D ck proof pub v hash := rfl

theorem installed_writer (ops : Ops) (reserved : Bool) (unwrap : Unwrap)
    (other : VTop_OracleCode.Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) :
    implementation ops reserved unwrap other (.op8 D p a proof pub hash)=
      writer D p a proof pub hash := rfl

#print axioms reader_value
#print axioms writer_value
#print axioms reader_effects
#print axioms installed_reader
#print axioms installed_writer
end AspisR1.Port8EFF_Bodies
end
