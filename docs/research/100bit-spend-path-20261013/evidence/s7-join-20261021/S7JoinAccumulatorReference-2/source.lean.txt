import S7JoinQueryReference
import S7JoinProductionBasis

/-! Total field-reference refinement to the exact arithmetic consumer of
 dV_frozen. Source byte decoding, query rejection and TX membership are separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7JoinAccumulatorReference
open AspisCircleGroupOrder AspisCircleTensorBinding
open S7JoinQueryReference
variable {K E : Type} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) K] [Algebra (ZMod P) E]

/-- Production-shaped field reference, using the proved stored line fold and
six-factor basis rather than the consumer's already-closed sums. -/
def run (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) : QueryAccumulator.State K E :=
  QueryAccumulator.run22 iota rho
    (fun j => queryValue data.alpha1 data.V (parentIndex (q j)))
    (queryBasis q)

theorem run_eq (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) :
    run iota data q rho = QueryAccumulator.run22 iota rho
      (QueryResidualBridge.values data q) (QueryResidualBridge.basis q) := by
  have hv : (fun j => queryValue data.alpha1 data.V (parentIndex (q j))) =
      QueryResidualBridge.values data q := funext (fun j => query_values_eq data q j)
  have hb : queryBasis (K:=K) q=QueryResidualBridge.basis q :=
    funext (fun j => funext (fun l => query_basis_eq q j l))
  simp only [run,hv,hb]

/-- Both directions, all field inputs, with no successful-run hypothesis. -/
theorem check_iff_closed_sum (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) :
    (∑ l : Fin 64, data.f l*iota ((run iota data q rho).weights l)) =
      (run iota data q rho).rhs ↔ HchecksAccumulator.ClosedSum iota data q rho := by
  rw [run_eq]
  simp only [QueryAccumulator.run22_weights,QueryAccumulator.run22_rhs,
    HchecksAccumulator.ClosedSum]

/-- The exact emitted basis is also valid after embedding into the challenge
field. This conclusion is total over U32, not just canonical input words. -/
theorem emitted_basis (node : Aeneas.Std.U32) : ∃ out,
    S7JoinProductionBasis.basis_owned node=Aeneas.Std.Result.ok out ∧
    ∀ l : Fin 64,
      algebraMap (ZMod P) K
        (S7JoinBasisMachine.decode (S7JoinBasisBlock.cell out l.val)) =
      naturalLineValue (algebraMap (ZMod P) K (S7JoinBasisMachine.decode node)) l.val := by
  obtain ⟨out,ho,hcells⟩ := S7JoinProductionBasis.total_exact node
  refine ⟨out,ho,?_⟩
  intro l
  rw [hcells l,NaturalEmbedding.map_naturalLineValue]

#print axioms run_eq
#print axioms check_iff_closed_sum
#print axioms emitted_basis
end AspisR1.S7JoinAccumulatorReference
