import AspisFormal.Pool.V7FixedWidth29TupleList

/- Research only: a slightly larger mathematical family, not a deployed decoder.
   This settles cardinality and completeness ABOVE A JOINT CLOSENESS FLOOR.
   It does not prove that accepted adaptive branches are close to this family. -/
set_option autoImplicit false
namespace AspisV8ResearchRelaxedFamily
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7Width29ComponentExtraction
open AspisPool.V7FixedWidth29TupleList
open AspisV5ComponentCQM31TowerExact
open AspisV6Width29CorrelatedAgreement
open AspisV5FriJohnsonListBound

theorem relaxed_joint_family_card_le_100
    (lanes : Width29InitialWords QM31Exact)
    (candidates : Finset (Width29InitialMessages QM31Exact))
    (large : ∀ components ∈ candidates, 38228 ≤
      (width29JointAgreementSet exactInitialEncoder lanes components).card) :
    candidates.card ≤ 100 := by
  classical
  let Candidate := {components // components ∈ candidates}
  let agreement : Candidate → Finset (Fin 1048576) := fun c =>
    width29JointAgreementSet exactInitialEncoder lanes c.1
  have hlarge : ∀ c : Candidate, 38228 ≤ (agreement c).card := by
    intro c
    exact large c.1 c.2
  have hoverlap : ∀ c d : Candidate, c ≠ d →
      ((agreement c) ∩ (agreement d)).card ≤ 1024 := by
    intro c d different
    apply distinct_tuple_joint_agreement_overlap_le_1024 lanes c.1 d.1
    intro same
    exact different (Subtype.ext same)
  have forbidden : Fintype.card Candidate < 101 :=
    list_card_lt_of_johnson_parameters agreement 1048576 38228 1024 101
      (by simp) hlarge hoverlap (by norm_num) (by norm_num) (by norm_num)
  rw [Fintype.card_coe] at forbidden
  omega

/-- Abstract finite-universe construction. Keeping this generic avoids unfolding
    the enormous concrete message universe during elaboration of membership. -/
theorem finite_predicate_cover {A : Type*} [Fintype A]
    (predicate : A → Prop) (limit : Nat)
    (bound : ∀ candidates : Finset A,
      (∀ c ∈ candidates, predicate c) → candidates.card ≤ limit) :
    ∃ family : Finset A, family.card ≤ limit ∧
      ∀ c, predicate c → c ∈ family := by
  classical
  let family := Finset.univ.filter predicate
  refine ⟨family, bound family ?_, ?_⟩
  · intro c member
    exact (Finset.mem_filter.mp member).2
  · intro c property
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, property⟩

/-- Coverage of all CLOSE tuples is proved rather than assumed membership.
    No conclusion about arbitrary post-challenge candidates is hidden here. -/
theorem exists_small_family_covering_all_close_tuples
    (lanes : Width29InitialWords QM31Exact) :
    ∃ family : Finset (Width29InitialMessages QM31Exact), family.card ≤ 100 ∧
      ∀ components, 38228 ≤
        (width29JointAgreementSet exactInitialEncoder lanes components).card →
          components ∈ family := by
  exact finite_predicate_cover
    (fun components => 38228 ≤
      (width29JointAgreementSet exactInitialEncoder lanes components).card)
    100 (relaxed_joint_family_card_le_100 lanes)

/-- C1 descent needs the tuple's OWN large joint support, not containment of
    every selected combined-candidate agreement. Existing encoder projection
    bindings stay explicit; no decoder membership or new subfield axiom is used. -/
theorem relaxed_close_tuple_c1_is_base
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (lanes : Width29InitialWords QM31Exact)
    (components : Width29InitialMessages QM31Exact)
    (close : 38228 ≤
      (width29JointAgreementSet decoder.initialEncoder lanes components).card)
    (receivedFixed : ∀ column : Fin 26, ∀ index,
      projectBase (lanes (c1LaneIndex column) index) =
        lanes (c1LaneIndex column) index) :
    ∀ column : Fin 26,
      projectMessage (components (c1LaneIndex column)) =
        components (c1LaneIndex column) := by
  intro column
  apply message_fixed_by_base_projection_of_large_shared_support
    decoder binding lanes components
    (width29JointAgreementSet decoder.initialEncoder lanes components)
    column (Finset.Subset.refl _) (receivedFixed column)
  omega

#print axioms relaxed_joint_family_card_le_100
#print axioms finite_predicate_cover
#print axioms exists_small_family_covering_all_close_tuples
#print axioms relaxed_close_tuple_c1_is_base
end AspisV8ResearchRelaxedFamily
