import R1Z.PV_RunJoin_OpeningByteCodec51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleTapeState55

theorem decode (b : R0Z.FsStatement.OracleAnswer) :
    AspisV8R19.SqueezeOracleBridge.decodeState (PV_RunJoin_OpeningSampler50.block b)=
      (fun i => (b i).toFin) := by
  unfold PV_RunJoin_OpeningSampler50.block
  rw [AspisV8R19.SqueezeOracleBridge.state_roundtrip]
  rfl
#print axioms decode
end R1Z.PV_RunJoin_CircleTapeState55
