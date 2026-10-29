import R1Z.PV_RunJoin_InactiveThread48
import R1Z.PV_RunJoin_InactiveFields48
import R1Z.PV_RunJoin_WeightRawInstalled46
import R1Z.PV_RunJoin_OpeningResult48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveCell48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)
open ProverRwDictionaryTower (fromW toW fromQ toQ native_w_roundtrip native_q_roundtrip)
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Source := AspisR1ProducerRelease47.field.wide_exact.WideExact

def step (q : Slice W) (state : ProverCommitWeightsStorage53.State) (sum : Source) (row : Usize) : Result Source := do
  let value ← mapResult toW (Slice.index_usize q row)
  let raw ← AspisR1ProducerRelease47.weights53.raw state 0#usize row
  let product ← AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_qm31 value raw
  AspisR1ProducerRelease47.field.wide_exact.WideExact.add sum product

theorem raw_carrier (q : AspisR1ProducerRelease47.field.QM31) :
    PV_RunJoin_WeightRawInstalled46.nativeQ q=fromQ q := by cases q;rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Slice W) (w : PV_RunJoin_WeightCarrier46.W)
    (hs : w.variant=.S2) (sum : Source) (row : Usize) :
    @PV_RunJoin_InactiveThread48.step (types base) (selected base heap box ops) q w (fromW sum) row=
      mapResult fromW (step q (PV_RunJoin_WeightCarrier46.state w) sum row) := by
  unfold PV_RunJoin_InactiveThread48.step step
  rw [show @weights.Weights.raw (types base) (selected base heap box ops) w 0#usize row=_
    from PV_RunJoin_WeightRawInstalled46.raw0 base heap box ops w hs row]
  simp only [aspis_core.field.wide_exact.WideExact.mul_qm31,
    aspis_core.field.wide_exact.WideExact.add,PV_RunJoin_InactiveFields48.mul,
    PV_RunJoin_InactiveFields48.add]
  rw [PV_RunJoin_OpeningResult48.map_after]
  cases hread : Slice.index_usize q row with
  | fail e => rfl
  | div => rfl
  | ok value =>
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok]
    cases hr : AspisR1ProducerRelease47.weights53.raw (PV_RunJoin_WeightCarrier46.state w) 0#usize row with
    | fail e => rfl
    | div => rfl
    | ok raw =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,raw_carrier,
        ProverRwDictionaryWideQM.mul,native_q_roundtrip,PV_RunJoin_OpeningResult48.tower]
      rw [PV_RunJoin_OpeningResult48.bind_map]
      apply congrArg (Aeneas.Std.bind _)
      funext product
      simp only [ProverRwDictionaryTower.wAdd,native_w_roundtrip,PV_RunJoin_OpeningResult48.tower]
#print axioms raw_carrier
#print axioms complete
end R1Z.PV_RunJoin_InactiveCell48
