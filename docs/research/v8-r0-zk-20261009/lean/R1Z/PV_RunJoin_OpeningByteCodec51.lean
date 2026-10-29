import R1Z.PV_RunJoin_OpeningBlockEquiv50
import R1Z.ProverRwOuterFrames
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningByteCodec51
open Aeneas Aeneas.Std R0Z.FsStatement
open ProverCommitOwnerBytes42 (byte)

theorem byte_encode (b : Fin 256) : byte (AspisV8R19.SqueezeOracleBridge.encodeByte b)=UInt8.ofFin b := by
  apply UInt8.eq_of_toNat_eq
  rfl

theorem bytes (b : OracleAnswer) :
    (PV_RunJoin_OpeningSampler50.block b).val.map byte=LensR1.ans b := by
  unfold PV_RunJoin_OpeningSampler50.block PhaseSamplerParserBin.state
    AspisV8R19.SqueezeOracleBridge.encodeState AspisV8R19.SourceDuplexStep.bytes LensR1.ans
  rw [List.map_map]
  simp only [List.map_ofFn,Function.comp_def,byte_encode,R1J.SamplerLawSpend.stateEquiv,
    Equiv.coe_fn_mk,UInt8.ofFin_toFin]

theorem actual_bytes (b : Array U8 32#usize) :
    b.val.map byte=LensR1.ans (PV_RunJoin_OpeningBlock50.answer b) := by
  rw [←PV_RunJoin_OpeningBlock50.roundtrip b]
  exact bytes _
#print axioms byte_encode
#print axioms bytes
#print axioms actual_bytes
end R1Z.PV_RunJoin_OpeningByteCodec51
