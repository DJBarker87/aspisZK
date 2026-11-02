import R1Z.PV_RunJoin_NativeQuarticTotal69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQuarticEq72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem eq (a b : Q) :
    @aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq (types base)
      (opsNative base heap box ops runtime world) a b=ok (decide (a=b)) := by
  change @ExternalFuns.op63 (types base) (opsNative base heap box ops runtime world) a b=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_63]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  exact ProverRwDictionaryDerived.q_status a b

theorem ne_self (a : Q) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a a=ok false := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    eq base heap box ops runtime world,bind_tc_ok]
  rfl

#print axioms eq
#print axioms ne_self
end R1Z.PV_RunJoin_NativeQuarticEq72
