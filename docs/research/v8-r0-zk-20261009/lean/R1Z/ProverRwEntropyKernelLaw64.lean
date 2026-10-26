import R1Z.ProverRwEntropyPartition64
import R1Z.ProverRwEntropyKernelRate64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyKernelLaw64
open ProverCommitPublicNonce40 ProverRwEntropyKernel64 ProverRwEntropyTermination64
open ProverRwEntropyPartition64 ProverRwEntropyUniform64
open scoped BigOperators

/-- Exact sixteen-fill success marginal, with all missing mass named.
This requires E1 at the explicitly supplied context and is not a native
callback adequacy theorem. Joint post-context/secret independence is not asserted. -/
theorem sixteen_law {C : Type} [Fintype C]
    (available : C → ℚ) (law : C → Raw → ℚ) (next : C → Raw → C → ℚ)
    (stop : Stop → C → C → ℚ) (entropy_law : E1 law)
    (transition : ∀ c raw, ∑ after : C, next c raw after = 1)
    (complement : ∀ c, stopHead stop c = 1 - available c) (c : C) (secret : Private) :
    marginal (arrival available law next) (retry available law next) 16 c secret =
      (1 - stopMass stop (retry available law next) 16 c -
        zeroMass (retry available law next) 16 c) / (Fintype.card Private : ℚ) := by
  have total := conservation (arrival available law next) stop (retry available law next)
    (e1_step_conservation available law next stop entropy_law transition complement) 16 c
  have accepted : successMass available law next 16 c =
      1 - stopMass stop (retry available law next) 16 c -
        zeroMass (retry available law next) 16 c := by
    change successMass available law next 16 c + _ + _ = 1 at total
    linarith only [total]
  rw [sixteen_factor available law next entropy_law transition,accepted]

/-- Eight outer attempts can charge the sixteen-fill exhaustion hazard,
provided the actual outer transition is subsequently shown substochastic.
No independence between outer attempts is required or asserted. -/
theorem eight_exhaustion {C : Type} [Fintype C]
    (hazard : C → ℚ) (again : C → C → ℚ)
    (small : ∀ c, hazard c ≤ ProverRwEntropyAbort64.zeroBudget^16)
    (nonnegative : ∀ c d, 0 ≤ again c d) (mass : ∀ c, ∑ d, again c d ≤ 1) (c : C) :
    ProverRwEntropyKernelBounds64.campaign hazard again 8 c ≤
      8 * ProverRwEntropyAbort64.zeroBudget^16 := by
  apply ProverRwEntropyKernelBounds64.eight_bound
  · unfold ProverRwEntropyAbort64.zeroBudget
    positivity
  · exact nonnegative
  · exact mass
  · exact small

#print axioms sixteen_law
#print axioms eight_exhaustion
end R1Z.ProverRwEntropyKernelLaw64
