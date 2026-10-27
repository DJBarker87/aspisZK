import ARQ_SamplerCongr
import ARQ_AcceptedRows
import F3T_Canon
import F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_PreparedSampler
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem same {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (s : F3T_ByteCarrier.Submission) (accepted : (eval H (F3_Model.verifier D i)).2 = true)
    (semantic : i.semantic = (F3T_ByteCarrier.input c s).semantic) (stored : i.stored = s.stored) :
    (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 =
      (eval H (F3J_SamplerRun.program
        (F3T_Canon.canonInput (F3T_ByteCarrier.input c s)).proof 0 33
        (FS.emptyPrefix (F3T_ByteCarrier.input c s).semantic.value))).1 := by
  apply (ARQ_SamplerCongr.run H i.proof
    (F3T_Canon.canonInput (F3T_ByteCarrier.input c s)).proof 0 33 _ _ ?_ ?_).1
  · intro j below
    simp only [Nat.zero_add]
    rw [ARQ_AcceptedRows.stored D H i accepted j below,stored]
    exact (R16CanonReduction.erase_proof (Port1_StoredCarrier.proof s.stored) j).symm
  · rw [semantic]

#print axioms same
end AspisR1.ARQ_PreparedSampler
end
