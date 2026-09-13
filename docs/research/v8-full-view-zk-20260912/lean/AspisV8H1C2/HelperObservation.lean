import AspisV8H1C2.Incidence
import AspisV8H1C2.NonlinearFreshPad

/-! Conditional fixed-linear H1 observation endpoint. The literal Rust
registry supplies `src`/`dst`; honest constraint validation supplies complete
active-tuple matching; helper success supplies the pole-free premise; and a
separate ideal-expander/prefix theorem must supply fresh uniform `U` coins. -/
set_option autoImplicit false
namespace AspisV8H1C2
noncomputable section

variable {Edge Row K U Obs : Type*}
  [Fintype Edge] [DecidableEq Row] [Field K]
  [AddCommGroup U] [Module K U] [Fintype U] [Nonempty U]
  [AddCommGroup Obs] [Module K Obs]

theorem fixed_helper_observation_uniform
    (src dst : Edge → Row) (weight prod cons : Edge → K) (chi : K)
    (matching : ∀ edge, weight edge ≠ 0 → prod edge = cons edge)
    (_poleFree : PoleFree weight prod cons chi)
    (P : U →ₗ[K] (Row → K)) (L : (Row → K) →ₗ[K] Obs)
    (C : (Edge → K) →ₗ[K] U)
    (covers : (L.comp P).comp C = L.comp (incidenceMap src dst)) :
    SameUniformLaw
      (fun u => L (helperByRows src dst weight prod cons chi + P u))
      (fun u => L (P u)) := by
  rw [helper_eq_incidence src dst weight prod cons chi matching]
  change SameUniformLaw
    (fun u => L ((incidenceMap src dst)
      (fun edge => coeff (weight edge) chi (prod edge)) + P u))
    (fun u => L (P u))
  have transported := covered_nonlinear_offset_uniform
    (M := L.comp P) (B := L.comp (incidenceMap src dst)) C covers
    (fun _ : Unit => fun edge => coeff (weight edge) chi (prod edge)) ()
  simpa only [LinearMap.comp_apply, map_add] using transported

#print axioms fixed_helper_observation_uniform
end
end AspisV8H1C2
