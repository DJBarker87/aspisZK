import FJh_InternalPrepare

/-! Complete source refinement of internal_linear_lazy to the existing
exact-field Poseidon internal-linear model, with canonical output. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalLinearExact
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base
open AspisR1.FJh_InternalAccumulatorModel (partSum)
open AspisR1.FJh_InternalLaneReassembly (rawDecode)
open AspisR1.FJh_InternalLaneStep (laneModel diagonal)

theorem source_success (state : State) (hstate : CanonicalState state) :
    ∃ out : State, state_only_poseidon.internal_linear_lazy state = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        R0P.poseidonInternalLinear (fun i : Fin 16 => Decode (cell state i)) j := by
  obtain ⟨state1,full,hprepare,hcan,hfullBound,hfullModel,hcells⟩ :=
    AspisR1.FJh_InternalPrepare.source_success state hstate
  obtain ⟨out,hrun,houtCan,houtModel⟩ :=
    AspisR1.FJh_InternalLaneLoop.source_success state1 full hcan hfullBound
  refine ⟨out,?_,houtCan,?_⟩
  · rw [AspisR1.FJh_InternalPrepare.wrapper_factor,hprepare,bind_tc_ok]
    exact hrun
  · intro j
    have h := houtModel j
    have hc := hcells j
    by_cases hz : j.val = 0
    · rw [if_pos hz] at h hc
      simp only [R0P.poseidonInternalLinear,dif_pos hz,if_pos hz]
      change Decode (cell out j) = partSum state - Decode (cell state (0 : Fin 16))
      exact h.trans hc
    · rw [if_neg hz] at h hc
      change Decode (cell out j) = rawDecode full + Decode (cell state1 j) * diagonal j at h
      have hm : Decode (cell out j) =
          (partSum state + Decode (cell state (0 : Fin 16))) + Decode (cell state j) * diagonal j := by
        rw [hfullModel,hc] at h
        exact h
      simp only [R0P.poseidonInternalLinear,dif_neg hz,if_neg hz]
      exact hm

#print axioms source_success
end AspisR1.FJh_InternalLinearExact
