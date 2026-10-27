import R1Z.PV_Src_PortSboxModel
import R1Z.PV_Src_ExternalModel

/-! The actual initial and final nonlinear-loop/external-call combinations
implement one full model round at the explicit owned dictionary. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortFullRoundModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
variable {K : Type} [Field K] [CharP K 2147483647]

def initial (s c : State) : Result State := do
  let nonlinear ← poseidon2.permute_optimized_with_trace_loop0_loop0
    {start := 0#usize, «end» := 16#usize} s c
  @poseidon2.external_linear_lazy PV_Src_ExternalReference.dictionary nonlinear

def final_round (s c : State) : Result State := do
  let nonlinear ← poseidon2.permute_optimized_with_trace_loop2_loop0
    {start := 0#usize, «end» := 16#usize} s c
  @poseidon2.external_linear_lazy PV_Src_ExternalReference.dictionary nonlinear

theorem initial_model (s c : State) (hs : Canonical s) (hc : Canonical c) : ∃ out,
    initial s c = ok out ∧ Canonical out ∧ ∀ j : Fin 16,
      liftU (K := K) out.val[j.val]! = R0P.poseidonFullRound (liftA s) (liftA c) j := by
  obtain ⟨nonlinear,hn,hcan,hN⟩ := PV_Src_PortSboxModel.initial (K := K) s c hs hc
  obtain ⟨out,ho,hoc,hO⟩ := PV_Src_ExternalModel.source (K := K) nonlinear
  refine ⟨out,by rw [initial,hn];simpa only [bind_tc_ok,PV_Src_ExternalReference.call_eq] using ho,hoc,?_⟩
  intro j
  rw [hO j]
  have hstate : liftA (K := K) nonlinear =
      fun i => R0P.poseidonPow5 (liftA (K := K) s i+liftA (K := K) c i) := by
    funext i;exact hN i
  rw [hstate]
  rfl

theorem final_model (s c : State) (hs : Canonical s) (hc : Canonical c) : ∃ out,
    final_round s c = ok out ∧ Canonical out ∧ ∀ j : Fin 16,
      liftU (K := K) out.val[j.val]! = R0P.poseidonFullRound (liftA s) (liftA c) j := by
  obtain ⟨nonlinear,hn,hcan,hN⟩ := PV_Src_PortSboxModel.final_round (K := K) s c hs hc
  obtain ⟨out,ho,hoc,hO⟩ := PV_Src_ExternalModel.source (K := K) nonlinear
  refine ⟨out,by rw [final_round,hn];simpa only [bind_tc_ok,PV_Src_ExternalReference.call_eq] using ho,hoc,?_⟩
  intro j
  rw [hO j]
  have hstate : liftA (K := K) nonlinear =
      fun i => R0P.poseidonPow5 (liftA (K := K) s i+liftA (K := K) c i) := by
    funext i;exact hN i
  rw [hstate]
  rfl

#print axioms initial_model
#print axioms final_model
end R1Z.PV_Src_PortFullRoundModel
