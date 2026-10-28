import R1Z.PV_RunJoin_WeightKernel46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightConstructorThread46
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows PV_B2_C_WeightsNative
abbrev V := PV_B2_C_Carrier.transport.Variant
abbrev K := PV_B2_F_ConstructorCarrier.K
abbrev Point := PV_B2_F_ConstructorCarrier.Point

def rows (p : Points) (z : Array Point 2#usize) (f : Factors) : Result Factors := do
  let f0 ← row0 f p
  let f1 ← row1 f0 p
  let f2 ← row2 f1 p
  let f3 ← row3 f2 z
  row4 f3 z

def run (v : V) (alpha : Array K 10#usize) (z : Array Point 2#usize) := do
  let p ← host_weights.state_only_statement_points alpha
  let a8 ← Array.index_usize alpha 8#usize
  let a9 ← Array.index_usize alpha 9#usize
  let f ← rows p z (Array.repeat 5#usize (Array.repeat 5#usize
    (Array.repeat 4#usize aspis_core.field.QM31.ZERO)))
  ok (.Ok ({variant:=v,factors:=f,points:=p,extra:=Array.make 2#usize [a8,a9]} : host_weights.Weights) :
    core.result.Result host_weights.Weights PV_B2_C_Carrier.verifier.Error)

attribute [local irreducible] host_weights.state_only_statement_points row0 row1 row2 row3 row4

theorem complete (v : V) (alpha : Array K 10#usize) (z : Array Point 2#usize) :
    host_weights.Weights.new v alpha z=run v alpha z := by
  rw [PV_B2_C_ConstructorSuccess.new_eq_staged]
  simp only [PV_B2_C_ConstructorSuccess.staged,
    PV_B2_C_ConstructorStages.stage0_eq,PV_B2_C_ConstructorStages.stage1_eq,
    PV_B2_C_ConstructorStages.stage2_eq,PV_B2_C_ConstructorStages.stage3_eq,
    PV_B2_C_ConstructorStages.stage4_eq,run,rows,bind_assoc,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_WeightConstructorThread46
