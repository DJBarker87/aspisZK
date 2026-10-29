import R1Z.PV_RunJoin_InactiveFinite48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveRun48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_InactiveCell48 (W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Slice W) (w : PV_RunJoin_WeightCarrier46.W)
    (hs : w.variant=.S2) :
    @prover.opening_inactive (types base) (selected base heap box ops) q w=
      mapResult fromW (PV_RunJoin_InactiveFinite48.run 1024 q
        (PV_RunJoin_WeightCarrier46.state w)
        AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO 0#usize) := by
  unfold prover.opening_inactive
  rw [show @aspis_core.field.wide_exact.WideExact.ZERO (types base) (selected base heap box ops)=_
    from PV_RunJoin_InactiveFields48.zero base heap box ops]
  simp only [bind_tc_ok]
  rw [@PV_RunJoin_InactiveThread48.complete (types base) (selected base heap box ops)
    q w _ 0#usize 1024 (by decide)]
  exact PV_RunJoin_InactiveFinite48.complete base heap box ops q w hs _ _ _
#print axioms complete
end R1Z.PV_RunJoin_InactiveRun48
