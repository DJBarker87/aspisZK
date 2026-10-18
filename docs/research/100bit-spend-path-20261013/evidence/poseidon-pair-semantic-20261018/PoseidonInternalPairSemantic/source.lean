import PoseidonInternalPairExact
import PoseidonPairMap
import ExtractedMaskSemanticBridgeConcrete

/-! Transport the checked actual internal-pair caller into the existing
WideExact semantic carrier. This uses the maintained concrete algebra map;
it adds no source-success premise or replacement semantic relation. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInternalPairSemantic
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State Exact Decode CanonicalState cell)
abbrev Wide := AspisWideTower.WideExact
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide

theorem source_success (state local1 : State) (hstate : CanonicalState state)
    (hlocal : CanonicalState local1) :
    ∃ out : State, state_only_poseidon.interpolated_internal_pair state local1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16,
        f (Decode (cell out j)) = R0P.poseidonInterpolatedInternalPair
          (fun i : Fin 16 => f (Decode (cell state i)))
          (fun i : Fin 16 => f (Decode (cell local1 i))) j := by
  obtain ⟨out,hrun,hcan,hmodel⟩ :=
    AspisR1.PoseidonInternalPairExact.source_success state local1 hstate hlocal
  refine ⟨out,hrun,hcan,?_⟩
  intro j
  have hnatural := congrFun
    (AspisR1.PoseidonPairMap.map_poseidonInterpolatedInternalPair f
      (fun i : Fin 16 => Decode (cell state i))
      (fun i : Fin 16 => Decode (cell local1 i))) j
  exact (congrArg f (hmodel j)).trans hnatural

#print axioms source_success
end AspisR1.PoseidonInternalPairSemantic
