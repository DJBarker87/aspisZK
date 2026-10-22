import S4V10CandidateQueryFieldEvidenceV1
import ExtractedCurrentTowerAdd

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10CandidateQueryFullWideBoundsV1

open AspisR1Stage2
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE)
open AspisR1S4FullQueryValuesPrefixV1

abbrev FullWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev P : Nat := 2147483647

def FullCoordinateBound (x : FullWide) : Prop :=
  x.c0.c0.a.val < P ∧ x.c0.c0.b.val < P ∧
  x.c0.c1.a.val < P ∧ x.c0.c1.b.val < P ∧
  x.c1.c0.a.val < P ∧ x.c1.c0.b.val < P ∧
  x.c1.c1.a.val < P ∧ x.c1.c1.b.val < P

theorem current_wide_to_full_preserves_canonical
    (x : CurrentWide)
    (h : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) :
    FullCoordinateBound (currentWideToFull x) := by
  change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x).c0 ∧
    AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x).c1 at h
  change AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1CurrentWide.Proof.toQM
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x).c0) ∧
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1CurrentWide.Proof.toQM
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x).c1) at h
  simp only [AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
    AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE,
    AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentQM,
    AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentCM] at h
  rcases h with ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩

theorem current_array_to_full_preserves_canonical
    (xs : Array CurrentWide 4#usize)
    (h : ∀ x ∈ xs.val,
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) :
    ∀ x ∈ (currentArrayToFull xs).val, FullCoordinateBound x := by
  intro x hx
  have hmem : ∃ y ∈ xs.val, currentWideToFull y = x := by
    exact List.mem_map.mp hx
  obtain ⟨y,hy,rfl⟩ := hmem
  exact current_wide_to_full_preserves_canonical y (h y hy)

theorem candidate_query_fullwide_coordinate_bounds
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (claimPowers : Array ClaimE 29#usize)
    (he : CandidateQueryFieldEvidence rest proof p a g claimPowers) :
    ∃ (i : U32) (u : Usize) (q : Slice U8)
      (candidateValues : Array FullWide 4#usize),
      sourceOpening proof a.next = .ok q ∧
      (concreteCandidateQueryOps rest).dots q g = .ok candidateValues ∧
      (∀ x ∈ candidateValues.val, FullCoordinateBound x) := by
  rcases he with ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,
    hi,hu,hopening,hread,hcall,hmap,ha,hcanon,hlist,hf0,hf1,hf2,hf3⟩
  refine ⟨i,u,q,candidateValues,hopening,hcall,?_⟩
  intro x hx
  rw [← hmap] at hx
  exact current_array_to_full_preserves_canonical currentValues hcanon x hx

#print axioms current_wide_to_full_preserves_canonical
#print axioms current_array_to_full_preserves_canonical

end AspisR1FastDotsV10CandidateQueryFullWideBoundsV1
