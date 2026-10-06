import AspisFormal.V6Width29CorrelatedAgreement

/-! Simultaneous separation of a finite family of 29-tuples. Each unordered
pair excludes at most 28 nonzero challenges. All cardinality arguments are
symbolic; no enumeration of the challenge field is evaluated. -/
set_option autoImplicit false
namespace AspisWide.BatchSeparation
open AspisV6Width29CorrelatedAgreement

variable {K Coord : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable def pairCollisions (pair : Finset (Fin 29 → Coord → K)) : Finset K := by
  classical
  exact (Finset.univ.erase 0).filter fun z =>
    ¬ Set.InjOn (fun t => width29CurveValue t z) (pair : Set (Fin 29 → Coord → K))

theorem pairCollisions_card_le (pair : Finset (Fin 29 → Coord → K))
    (two : pair.card = 2) : (pairCollisions pair).card ≤ 28 := by
  classical
  obtain ⟨left, right, different, rfl⟩ := Finset.card_eq_two.mp two
  have coordinate : ∃ x, (fun i => left i x - right i x) ≠ 0 := by
    by_contra none
    push Not at none
    apply different
    funext i x
    exact sub_eq_zero.mp (congrFun (none x) i)
  obtain ⟨x, discrepancy⟩ := coordinate
  apply (Finset.card_le_card (show pairCollisions {left, right} ⊆
      width29NonzeroCollisionSet (fun i => left i x - right i x) from ?_)).trans
    (width29_nonzero_collision_card_le _ discrepancy)
  intro z hz
  have hz' := Finset.mem_filter.mp hz
  have collision : width29CurveValue left z = width29CurveValue right z := by
    by_contra no
    apply hz'.2
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.injOn_pair] using
      (fun h => (no h).elim : width29CurveValue left z = width29CurveValue right z → left = right)
  apply Finset.mem_filter.mpr
  refine ⟨hz'.1, ?_⟩
  have atCoordinate := congrFun collision x
  simp only [width29CurveValue, width29Batch] at atCoordinate ⊢
  simp only [sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr atCoordinate

/-- Outside at most `choose(card family,2)*28` roots, every batch is distinct. -/
theorem exists_nonzero_injective_batch (family : Finset (Fin 29 → Coord → K))
    (room : family.card.choose 2 * 28 < Fintype.card K - 1) :
    ∃ z : K, z ≠ 0 ∧
      Set.InjOn (fun t => width29CurveValue t z) (family : Set (Fin 29 → Coord → K)) := by
  classical
  let bad := (family.powersetCard 2).biUnion pairCollisions
  have badCap : bad.card ≤ family.card.choose 2 * 28 := by
    calc
      bad.card ≤ (family.powersetCard 2).card * 28 :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun pair hp =>
          pairCollisions_card_le pair (Finset.mem_powersetCard.mp hp).2)
      _ = family.card.choose 2 * 28 := by rw [Finset.card_powersetCard]
  have fewer : bad.card < (Finset.univ.erase (0 : K)).card := by
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
      using badCap.trans_lt room
  obtain ⟨z, hz, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card fewer
  refine ⟨z, (Finset.mem_erase.mp hz).1, ?_⟩
  intro left hl right hr collision
  by_contra different
  apply outside
  apply Finset.mem_biUnion.mpr
  refine ⟨{left, right}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hl, hr⟩
  · simp [different]
  · apply Finset.mem_filter.mpr
    refine ⟨hz, ?_⟩
    intro injective
    exact different (injective (by simp) (by simp) collision)

#print axioms pairCollisions_card_le
#print axioms exists_nonzero_injective_batch
end AspisWide.BatchSeparation
