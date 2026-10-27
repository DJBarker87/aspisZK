import RPz8_F3R_PublicLog
set_option autoImplicit false
namespace AspisR1.F3R_InitUnique
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceGlobalOracleInitial

theorem pair {H : Type} {D : aspis_core.Digest32 H}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : Array U8 32#usize} {before : r1_wire.SemanticTranscript H}
    (a b : PublicInitCall D pub root before) : initPair a=initPair b := by
  have encoded : a.encoded=b.encoded := core.result.Result.Ok.inj (Result.ok.inj (a.serialized.symm.trans b.serialized))
  have converted := a.converted
  rw [encoded] at converted
  have length : a.length=b.length := core.result.Result.Ok.inj (Result.ok.inj (converted.symm.trans b.converted))
  have digest := a.digest
  rw [encoded,length] at digest
  have state : a.state=b.state := Result.ok.inj (digest.symm.trans b.digest)
  unfold initPair
  rw [encoded,length,state]

#print axioms pair
end AspisR1.F3R_InitUnique
