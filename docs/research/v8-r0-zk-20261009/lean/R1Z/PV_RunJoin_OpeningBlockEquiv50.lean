import R1Z.PV_RunJoin_OpeningBlock50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningBlockEquiv50
open Aeneas Aeneas.Std
open R0Z.FsStatement

theorem inverse (b : OracleAnswer) :
    PV_RunJoin_OpeningBlock50.answer (PV_RunJoin_OpeningSampler50.block b)=b := by
  unfold PV_RunJoin_OpeningBlock50.answer PV_RunJoin_OpeningSampler50.block
  rw [AspisV8R19.SqueezeOracleBridge.state_roundtrip]
  exact R1J.SamplerLawSpend.stateEquiv.symm_apply_apply b

theorem association_iff (block : Array U8 32#usize) (b : OracleAnswer) :
    block=PV_RunJoin_OpeningSampler50.block b ↔ PV_RunJoin_OpeningBlock50.answer block=b := by
  constructor
  · intro h
    have e := congrArg PV_RunJoin_OpeningBlock50.answer h
    rw [inverse] at e
    exact e
  · intro h
    calc
      block=PV_RunJoin_OpeningSampler50.block (PV_RunJoin_OpeningBlock50.answer block) :=
        (PV_RunJoin_OpeningBlock50.roundtrip block).symm
      _=PV_RunJoin_OpeningSampler50.block b := congrArg PV_RunJoin_OpeningSampler50.block h
#print axioms inverse
#print axioms association_iff
end R1Z.PV_RunJoin_OpeningBlockEquiv50
