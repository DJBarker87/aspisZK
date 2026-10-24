import Port9OR_Code
import Port8EFF_Bodies
import Port8EFF_Budget

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Bodies
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port6CK_Semantic (Unwrap)

/-- Pointwise native primitive interpretation at the CONCRETE source type.
Only successful hashv bytes change; Copy and existing fail/div cases remain. -/
def native {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (H : Bytes → State) :
    aspis_core.digest.Digest32 Hash :=
  { D with digest := (Port9OR_Code.native (VTop_Checkpoint.digest D) H).digest }

theorem native_stage {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (H : Bytes → State) :
    VTop_Checkpoint.digest (native D H)=Port9OR_Code.native (VTop_Checkpoint.digest D) H := rfl

def reader (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) :=
  Port9OR_Code.program (VTop_Checkpoint.digest D) hash
    (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub v)

def writer {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : Hash) :=
  Port9OR_Code.program (VTop_Checkpoint.digest D) hash (Port8EFF_Bodies.writerCode p a proof pub)

/-- ALL inputs/outcomes. H occurs only in the pointwise native environment on
RHS, never as a parameter of the Program that is evaluated on LHS. -/
theorem reader_value (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) (H : Bytes → State) :
    (eval H (reader reserved unwrap D ck proof pub v hash)).2 =
      Port6CK_Reader.reader reserved unwrap (native D H) ck proof pub v hash := by
  rw [reader,Port9OR_Code.value,← native_stage]
  simp only [Port8EFF_Bodies.readerCode,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure]
  rw [Port8EFF_NativeReader.source]
  unfold Port6CK_Reader.reader
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out _
  cases out <;> rfl

theorem writer_value {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (hash : Hash) (H : Bytes → State) :
    (eval H (writer D p a proof pub hash)).2 =
      Port3_CheckpointInstall.writer (native D H) p a proof pub hash := by
  rw [writer,Port9OR_Code.value,← native_stage]
  simp only [Port8EFF_Bodies.writerCode,CheckpointBytes5Effect.erase_bind,CheckpointBytes5Effect.erase_pure]
  rfl

/-- Complete native reader correspondence, including malformed, rejected and
outer-failed suffixes, with no independently selected pair or successful map. -/
theorem reader_effects (reserved : Bool) (unwrap : Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : transport.Variant) (hash : Hash) (H : Bytes → State) :
    eval H (reader reserved unwrap D ck proof pub v hash)=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest (native D H)) hash
        (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub v)).1,
        Port6CK_Reader.reader reserved unwrap (native D H) ck proof pub v hash) := by
  apply Prod.ext
  · have h := congrArg Prod.fst (Port9OR_Code.correspondence (VTop_Checkpoint.digest D) hash
      (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub v) H)
    exact h
  · exact reader_value reserved unwrap D ck proof pub v hash H

theorem writer_effects {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (hash : Hash) (H : Bytes → State) :
    eval H (writer D p a proof pub hash)=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest (native D H)) hash
        (Port8EFF_Bodies.writerCode p a proof pub)).1,
        Port3_CheckpointInstall.writer (native D H) p a proof pub hash) := by
  apply Prod.ext
  · have h := congrArg Prod.fst (Port9OR_Code.correspondence (VTop_Checkpoint.digest D) hash
      (Port8EFF_Bodies.writerCode p a proof pub) H)
    exact h
  · exact writer_value D p a proof pub hash H

/-- Only owned op8/18 installed; all other source bodies remain explicit. -/
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

#print axioms native_stage
#print axioms reader_value
#print axioms writer_value
#print axioms reader_effects
#print axioms writer_effects
#print axioms installed_reader
#print axioms installed_writer
end AspisR1.Port9OR_Bodies
end
