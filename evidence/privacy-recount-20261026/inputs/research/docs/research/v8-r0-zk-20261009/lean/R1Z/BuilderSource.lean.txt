import R1Z.BuilderCanonical
import D18Transport

/-! The source handoff after the semantic builder proof.

The S2 coefficient transport is D18's involution (TAU=[3,4,2,0,1]).
`SourceIdentification` states precisely the source facts still needed before
calling a Rust prover an instance of this theorem. No such certificate for
the shipped compile functions is constructed here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderSource
open R0P R0Z.ZkStatement R0Z.HonestValidity
variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- S2 uses D18. It maps logical rows to coefficient positions; its inverse
is the same digit permutation, as proved by rowNat_involutive. -/
def π : Fin 1024 ≃ Fin 1024 := AspisR1.rowEquiv

/-- This orientation agrees with `Variant::coefficients`: coefficient j
is the physical semantic row `row(j)`. -/
theorem coefficients (t : Trace K) (c : Fin 29) (j : Fin 1024) :
    R0P.SemSource.coeffsOf π t c j = t c (AspisR1.row j) := rfl

/-- Reindexing the coefficients restores every raw semantic row. -/
theorem rows_coefficients (t : Trace K) :
    R0P.SemSource.rowsOf π (R0P.SemSource.coeffsOf π t) = t :=
  R0P.SemSource.rowsOf_coeffsOf π t

/-- The fully instantiated mathematical honest builder. -/
def prover : HonestProver K := BuilderCanonical.prover π

theorem public_map (w : BuilderCanonical.Instance (K := K)) :
    (prover (K := K)).public w = R1J.SpendWitnessMap.mapPub w.val.1 := rfl

theorem build_map (w : BuilderCanonical.Instance (K := K)) :
    (prover (K := K)).build w = BuilderRefinement.mergedTrace
      (BuilderCanonical.rustWitness w.val.2) (BuilderCanonical.rustPublic w.val.1) := rfl

theorem transport_map : (prover (K := K)).transport = π := rfl

/-- The builder premise is a theorem for this fixed π and canonical relation. -/
theorem builderSoundOn (hcard : 4096 < Fintype.card K) (F : Subfield K)
    (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn prover B x := BuilderCanonical.builderSoundOn hcard F π B x

/-- A source-only certificate: the map into the adopted honest relation,
public projection, raw trace output, and S2 transport. It assumes no lane,
base-typing, copy-balance, or helper fact. -/
structure SourceIdentification (source : HonestProver K)
    (toInstance : source.Instance → BuilderCanonical.Instance (K := K)) : Prop where
  public_eq : ∀ w, source.public w = prover.public (toInstance w)
  build_eq : ∀ w, source.build w = prover.build (toInstance w)
  transport_eq : source.transport = π

/-- The exact remaining source identification is sufficient to discharge
D46/D51 for the supplied source h. This theorem is conditional, not a
certificate for the shipped Rust entry points. -/
theorem builder_refinement_D46_D51 (hcard : 4096 < Fintype.card K) (F : Subfield K)
    (B : PackBasis F) (x : Statement K CommitHandle) (source : HonestProver K)
    (toInstance : source.Instance → BuilderCanonical.Instance (K := K))
    (identification : SourceIdentification source toInstance) :
    BuilderSoundOn source B x := by
  intro w hw
  rw [identification.build_eq w]
  exact builderSoundOn hcard F B x (toInstance w) ((identification.public_eq w).symm.trans hw)

#print axioms coefficients
#print axioms rows_coefficients
#print axioms public_map
#print axioms build_map
#print axioms transport_map
#print axioms builderSoundOn
#print axioms builder_refinement_D46_D51
end R1Z.BuilderSource
