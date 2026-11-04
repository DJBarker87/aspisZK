import R0Z.BuilderSound

/-! Builder completeness (t2b2b/DESIGN-BUILDER-COMPLETE.txt).

There is no concrete witness → trace builder in the Lean model (design §0):
`HonestProver.build` is an uninstantiated field and R0P is entirely in the
trace → witness direction.  This module therefore

* reduces the `lanes` field of `HonestBuilderCore` (laneOf = 0 for lanes
  0..27 at every λ, χ) to `NonCopyHolds`, the seven λ/χ-free production
  families, for every base-typed trace over a field with more than 4,096
  elements (`lanes_iff_nonCopy`, through the proved `lanes_zero_iff_holds`
  and a pole-free χ on the prepared instance);
* gives the constructive shape of the builder: 26 base-field semantic
  columns plus three extension columns (`ofColumns`), for which `baseTyped`
  is a theorem (`baseTyped_ofColumns`);
* states the two remaining builder facts, `NonCopyHolds` and
  `CopyLinkBalance` of the built trace for every witness in the relation,
  as the named refinement premise `BuilderRefines` against the Rust builder;
* gives the honest prover `honestProverOf` whose `build` is that builder,
  and proves `BuilderCoreOn` / `BuilderSoundOn` for it from the premise
  (`builderSoundOn_of_refines`), together with the soundness-side sanity
  check that its builds carry an extracted input note
  (`inputNoteExtracted_of_refines`).

The witness type `W` and relation `Rel` are parameters; the spend-path
instantiation is `W := Wspend`, `Rel := Rspend` (SpendRelation.lean). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderComplete
open R0P R0P.Sumcheck R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
open R0Z.HonestValidity R0Z.BuilderSound

attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### `lanes` is the non-copy production relation -/

/-- The seven production families that read neither λ, χ nor column 26. -/
def NonCopyHolds (pub : Public K) (t : Trace K) : Prop :=
  Holds valueFamily pub t ∧ Holds occupancyFamily pub t ∧ Holds assetFamily pub t ∧
  Holds scheduleFamily pub t ∧ Holds pathFamily pub t ∧ Holds digestFamily pub t ∧
  Holds poseidonScalarFamily pub t

theorem holds_prepare (f : Family K) (pub : Public K) (t : Trace K) (ch : Challenges K) :
    Holds f pub (prepare pub t ch) ↔ Holds f pub t := by
  simp only [Holds, rowOpenings_prepare]

theorem prepare_lt26 (pub : Public K) (t : Trace K) (ch : Challenges K) (c : Fin 29)
    (hc : c.val < 26) (b : Fin 1024) : prepare pub t ch c b = t c b := by
  unfold prepare
  exact if_neg (by omega)

theorem baseTyped_prepare (pub : Public K) (t : Trace K) (ch : Challenges K)
    (hA : BaseTyped F t) : BaseTyped F (prepare pub t ch) := fun c hc b => by
  rw [prepare_lt26 pub t ch c hc b]
  exact hA c hc b

/-- Lanes 0..27 do not read λ or χ. -/
theorem laneOf_lt_indep (t : Trace K) (pub : Public K) (lam chi lam' chi' : K)
    (B : PackBasis F) (i : Fin 29) (bits : Fin 10 → Bool) (hi : i.val < 28) :
    laneOf t pub lam chi B i bits = laneOf t pub lam' chi' B i bits := by
  unfold laneOf
  by_cases h4 : i.val < 4
  · simp only [dif_pos h4]
  · simp only [dif_neg h4, dif_pos hi]

/-- The LogUp pole values of a trace at λ: producer row-slot values on the
left, consumer row-slot values on the right. -/
def poleVal (t : Trace K) (lam : K) : (Fin 1024 × Fin 2) ⊕ (Fin 1024 × Fin 2) → K :=
  Sum.elim (fun p => copyRowValues t lam p.1 CopyLink.producer p.2)
    (fun p => copyRowValues t lam p.1 CopyLink.consumer p.2)

/-- Over a field with more than 4,096 elements, every λ has a pole-free χ:
the poles are at most 1024 rows × 2 slots × 2 endpoints values, so
`poleVal` is not surjective. -/
theorem exists_noPole (hcard : 4096 < Fintype.card K) (t : Trace K) (lam : K) :
    ∃ chi : K, NoPole t lam chi := by
  have hns : ¬ Function.Surjective (poleVal t lam) := by
    intro hs
    have h1 := Fintype.card_le_of_surjective (poleVal t lam) hs
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h1
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨chi, hchi⟩ := hns
  refine ⟨chi, fun b _ s => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have e := hchi (Sum.inl (b, s))
    simp only [poleVal, Sum.elim_inl] at e
    exact e h.symm
  · have e := hchi (Sum.inr (b, s))
    simp only [poleVal, Sum.elim_inr] at e
    exact e h.symm

/-- A challenge record with prescribed `sem 0 = λ`, `sem 1 = χ`. -/
def chOf (lam chi : K) : Challenges K :=
  ⟨fun j => if j.val = 0 then lam else chi, fun _ => ⟨(1, 0), by simp⟩, fun _ => 0, ∅⟩

theorem chOf_sem0 (lam chi : K) : (chOf lam chi).sem 0 = lam :=
  show (if (0 : Fin 25).val = 0 then lam else chi) = lam from if_pos rfl

theorem chOf_sem1 (lam chi : K) : (chOf lam chi).sem 1 = chi :=
  show (if (1 : Fin 25).val = 0 then lam else chi) = chi from if_neg (by decide)

/-- All 29 lanes vanish on the prepared instance at a pole-free challenge,
given the non-copy lanes of the raw trace. -/
theorem lanes_prepare_zero (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (hnp : NoPole t (ch.sem 0) (ch.sem 1))
    (hl : ∀ (i : Fin 29) (b : Fin 10 → Bool), i.val < 28 →
      laneOf t pub (ch.sem 0) (ch.sem 1) B i b = 0) :
    ∀ i b, laneOf (prepare pub t ch) pub (ch.sem 0) (ch.sem 1) B i b = 0 := by
  intro i b
  by_cases hi : i.val < 28
  · rw [laneOf_prepare_lt pub t ch _ _ B i b hi]
    exact hl i b hi
  · obtain rfl : i = 28 := Fin.ext (by have := i.isLt; omega)
    rw [laneOf_copy]
    exact copyHolds_prepare pub t ch hnp (rowOf b) _ (List.mem_singleton_self _)

/-- `lanes` of `HonestBuilderCore` is exactly `NonCopyHolds`, for base-typed
traces and base public inputs over a field with more than 4,096 elements. -/
theorem lanes_iff_nonCopy (hcard : 4096 < Fintype.card K) (B : PackBasis F)
    (pub : Public K) (t : Trace K) (hA : BaseTyped F t) (hpub : PublicBase F pub) :
    (∀ (lam chi : K) (i : Fin 29) (b : Fin 10 → Bool), i.val < 28 →
      laneOf t pub lam chi B i b = 0) ↔ NonCopyHolds pub t := by
  obtain ⟨chi0, hnp⟩ := exists_noPole hcard t 0
  let ch := chOf (0 : K) chi0
  have hnp' : NoPole t (ch.sem 0) (ch.sem 1) := by
    rw [chOf_sem0, chOf_sem1]; exact hnp
  have hAp := baseTyped_prepare pub t ch hA
  constructor
  · intro hl
    have hall := lanes_prepare_zero pub B t ch hnp' (fun i b hi => hl _ _ i b hi)
    obtain ⟨hv, ho, ha, hs, hp, hd, hpo, _⟩ :=
      (lanes_zero_iff_holds F B pub (ch.sem 0) (ch.sem 1) (prepare pub t ch) hAp hpub).mp hall
    exact ⟨(holds_prepare _ pub t ch).1 hv, (holds_prepare _ pub t ch).1 ho,
      (holds_prepare _ pub t ch).1 ha, (holds_prepare _ pub t ch).1 hs,
      (holds_prepare _ pub t ch).1 hp, (holds_prepare _ pub t ch).1 hd,
      (holds_prepare _ pub t ch).1 hpo⟩
  · rintro ⟨hv, ho, ha, hs, hp, hd, hpo⟩ lam chi i b hi
    have hc : CHolds copyFamily pub (ch.sem 0) (ch.sem 1) (prepare pub t ch) :=
      copyHolds_prepare pub t ch hnp'
    have hall := (lanes_zero_iff_holds F B pub (ch.sem 0) (ch.sem 1) (prepare pub t ch) hAp
      hpub).mpr ⟨(holds_prepare _ pub t ch).2 hv, (holds_prepare _ pub t ch).2 ho,
        (holds_prepare _ pub t ch).2 ha, (holds_prepare _ pub t ch).2 hs,
        (holds_prepare _ pub t ch).2 hp, (holds_prepare _ pub t ch).2 hd,
        (holds_prepare _ pub t ch).2 hpo, hc⟩
    rw [laneOf_lt_indep t pub lam chi (ch.sem 0) (ch.sem 1) B i b hi,
      ← laneOf_prepare_lt pub t ch _ _ B i b hi]
    exact hall i b

/-! ### The builder: constructive shape and refinement premise -/

/-- The builder's output shape: 26 base-field semantic columns (the Rust
`semantic_c1` M31 arrays) and three extension columns 26–28. -/
def ofColumns (c1 : Fin 26 → Fin 1024 → F) (rest : Fin 3 → Fin 1024 → K) : Trace K :=
  fun c r => if h : c.val < 26 then ((c1 ⟨c.val, h⟩ r : F) : K)
    else rest ⟨c.val - 26, by have := c.isLt; omega⟩ r

theorem baseTyped_ofColumns (c1 : Fin 26 → Fin 1024 → F) (rest : Fin 3 → Fin 1024 → K) :
    BaseTyped F (ofColumns c1 rest) := fun c hc b => by
  simp only [ofColumns, dif_pos hc]
  exact (c1 ⟨c.val, hc⟩ b).2

/-- The builder data: a public input and a witness determine the columns.
This is the Rust compile + host_semantic build, uninterpreted. -/
structure BuilderSpec (F : Subfield K) (W : Type) where
  c1 : Public K → W → Fin 26 → Fin 1024 → F
  rest : Public K → W → Fin 3 → Fin 1024 → K

def BuilderSpec.build {W : Type} (S : BuilderSpec F W) (pub : Public K) (w : W) : Trace K :=
  ofColumns (S.c1 pub w) (S.rest pub w)

/-- The refinement premise against the Rust builder: for every witness in
the relation, the built trace satisfies the seven non-copy production
families and every enabled copy link balances. -/
structure BuilderRefines {W : Type} (S : BuilderSpec F W) (Rel : Public K → W → Prop) : Prop where
  nonCopy : ∀ pub w, Rel pub w → NonCopyHolds pub (S.build pub w)
  balance : ∀ pub w, Rel pub w → CopyLinkBalance pub (S.build pub w)

/-- The honest prover whose `build` is the builder, on relation instances. -/
def honestProverOf {W : Type} (S : BuilderSpec F W) (Rel : Public K → W → Prop)
    (transport : Fin 1024 ≃ Fin 1024) : HonestProver K where
  Instance := {p : Public K × W // Rel p.1 p.2}
  transport := transport
  «public» := fun p => p.1.1
  build := fun p => S.build p.1.1 p.1.2

theorem builderCore_of_refines (hcard : 4096 < Fintype.card K) {W : Type}
    (S : BuilderSpec F W) (Rel : Public K → W → Prop) (hR : BuilderRefines S Rel)
    (B : PackBasis F) (pub : Public K) (hpub : PublicBase F pub) (w : W) (hw : Rel pub w) :
    HonestBuilderCore F pub B (S.build pub w) :=
  ⟨baseTyped_ofColumns _ _,
    (lanes_iff_nonCopy hcard B pub _ (baseTyped_ofColumns _ _) hpub).2 (hR.nonCopy pub w hw),
    hR.balance pub w hw⟩

theorem builderCoreOn_of_refines (hcard : 4096 < Fintype.card K) {W : Type}
    (S : BuilderSpec F W) (Rel : Public K → W → Prop) (hR : BuilderRefines S Rel)
    (transport : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (x : Statement K CommitHandle)
    (hpub : PublicBase F x.1) : BuilderCoreOn (honestProverOf S Rel transport) B x := by
  rintro ⟨⟨pub, w⟩, hw⟩ hx
  change pub = x.1 at hx
  subst hx
  exact builderCore_of_refines hcard S Rel hR B _ hpub w hw

theorem builderSoundOn_of_refines (hcard : 4096 < Fintype.card K) {W : Type}
    (S : BuilderSpec F W) (Rel : Public K → W → Prop) (hR : BuilderRefines S Rel)
    (transport : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (x : Statement K CommitHandle)
    (hpub : PublicBase F x.1) : BuilderSoundOn (honestProverOf S Rel transport) B x :=
  builderSoundOn_of_core _ B x (builderCoreOn_of_refines hcard S Rel hR transport B x hpub)

/-- Sanity check against soundness: a refined build carries an extracted
input note (R0P `input_note_extracted`), so the premise is the trace-side
image of the payment relation, not an unrelated condition. -/
theorem inputNoteExtracted_of_refines {W : Type} (S : BuilderSpec F W)
    (Rel : Public K → W → Prop) (hR : BuilderRefines S Rel) (pub : Public K) (w : W)
    (hw : Rel pub w) : InputNoteExtracted pub (S.build pub w) := by
  obtain ⟨_, _, ha, hs, hp, hd, hpo⟩ := hR.nonCopy pub w hw
  exact input_note_extracted pub _ hs hp hd ha hpo (hR.balance pub w hw)

#print axioms NonCopyHolds
#print axioms holds_prepare
#print axioms prepare_lt26
#print axioms baseTyped_prepare
#print axioms laneOf_lt_indep
#print axioms poleVal
#print axioms exists_noPole
#print axioms chOf
#print axioms chOf_sem0
#print axioms chOf_sem1
#print axioms lanes_prepare_zero
#print axioms lanes_iff_nonCopy
#print axioms ofColumns
#print axioms baseTyped_ofColumns
#print axioms BuilderSpec.build
#print axioms BuilderRefines
#print axioms honestProverOf
#print axioms builderCore_of_refines
#print axioms builderCoreOn_of_refines
#print axioms builderSoundOn_of_refines
#print axioms inputNoteExtracted_of_refines
end R0Z.BuilderComplete
