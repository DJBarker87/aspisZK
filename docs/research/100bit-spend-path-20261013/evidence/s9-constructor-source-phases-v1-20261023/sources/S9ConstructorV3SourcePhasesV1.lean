import S9ConstructorV3InitialFactorsCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3SourcePhasesV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev Vector := Array Q 10#usize
abbrev Points := Array Vector 3#usize
abbrev Circles := Array circle.SecureCirclePoint 2#usize

/-- Same accepted constructor execution supplies the actual point producer,
both complete factor phases and exact output fields, including the two
extra-coordinate source reads. No independent child success is assumed. -/
theorem constructor_success_source_phases
    (variant : Variant) (alpha : Vector) (z : Circles) (w : Weights)
    (hnew : weights_new variant alpha z = .ok (.Ok w)) :
    ∃ (points : Points) (q8 q9 : Q) (factors1 factors2 : Factors),
      state_only_prefix.r0.statement_points alpha = .ok points ∧
      Array.index_usize alpha 8#usize = .ok q8 ∧
      Array.index_usize alpha 9#usize = .ok q9 ∧
      weights_new_loop0 {start:=0#usize,«end»:=3#usize} points
        AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors = .ok factors1 ∧
      weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors1 = .ok factors2 ∧
      w = Weights.mk variant factors2 points (Array.make 2#usize [q8,q9]) := by
  unfold weights_new at hnew
  obtain ⟨points,hpoints,hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q8,hq8,hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q9,hq9,hnew⟩ := bind_success_inv _ _ _ hnew
  change (do
    let factors1 ← weights_new_loop0 {start:=0#usize,«end»:=3#usize} points
      AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors
    let factors2 ← weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors1
    let boxed ← Weights.box_from_parts variant factors2 points (Array.make 2#usize [q8,q9])
    ok (core.result.Result.Ok boxed)) = .ok (.Ok w) at hnew
  obtain ⟨factors1,hphase1,hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨factors2,hphase2,hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨boxed,hbox,hnew⟩ := bind_success_inv _ _ _ hnew
  have hboxed : boxed=w := core.result.Result.Ok.inj (Result.ok.inj hnew)
  subst boxed
  change Result.ok (Weights.mk variant factors2 points (Array.make 2#usize [q8,q9])) = Result.ok w at hbox
  have hw := Result.ok.inj hbox
  exact ⟨points,q8,q9,factors1,factors2,hpoints,hq8,hq9,hphase1,hphase2,hw.symm⟩

#print axioms constructor_success_source_phases
end AspisR1S9ConstructorV3SourcePhasesV1
