import R1Z.PV_RDCD5_FinalAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_FocusedReplay
open Aeneas Aeneas.Std Result ProverRwFull PV_CBL_LibraryShapes PV_CBL_GenericArrayPower

theorem v233 (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_AL_SplitNativeShape.Types base))
    (input : Slice U8) (origin : Nat) :
    letI : ProverRwFull.ExternalTypes := PV_AL_SplitNativeShape.Types base
    interpreted (PV_AL_SplitNativeShape.Size base 6) input origin =
      (@ProverRwFull.block_buffer.Eager.Insts.Block_bufferSealedSealed
        (PV_AL_SplitNativeShape.Types base)
        (PV_AL_SplitSelected.selected base ops)).split_blocks
          (PV_AL_SplitNativeShape.nativeTrait base ops 6) input := by
  exact PV_RDCD5_V233.consumed_instance base ops input origin
#print axioms v233

theorem v236 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_DL_UpdateSelected.Types base))
    {T N1 O : Type}
    (uc : @digest.core_api.UpdateCore (PV_DL_UpdateSelected.Types base) T N1 (Storage U8 6))
    (less : typenum.type_operators.IsLess (PV_AL_SplitNativeShape.Size base 6)
      (PV_DL_DefaultCallback.Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8)
    (hp : self.buffer.pos.val < 64) :
    @ExternalFuns.op216 (PV_DL_UpdateSelected.Types base)
      (PV_DL_UpdateSelected.selected base ops)
      T block_buffer.Eager (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6)
      N1 (Storage U8 6) O (PV_DL_UpdateSelected.bufferKind base ops T)
      uc less nz self input =
      typedSource (PV_DL_UpdateSelected.updater base uc) self input := by
  exact PV_RDCD5_V236.op216_instance base ops uc less nz self input hp
#print axioms v236

theorem v197_finding :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) ≠ PV_RDCD4_BytesSource.qm [] :=
  PV_RDCD5_ParserErrors.carrier_mismatch
#print axioms v197_finding
end R1Z.PV_RDCD5_FocusedReplay
