import RawAdaptiveClassifierHitDensity

/-! Per-step accounting, piece (b): the bad mass of every decoded start of R1's
adaptive literal decoder is at most the cap of that start's row class, where
the class is read from the start's address (the dispatch of
`UnifiedDecoder.decode`) and the public statement the decoder selects from
the address and the pre-read table.

Kind of result: a probability bound about R1's decoder and classifier (the
same level as R1's `RawAdaptiveClassifierHitDensity.adaptive_decoded_classifier_le`,
which it refines). It is about the R1 33-row protocol model, not about the
Aspis transcript; the Aspis instance extends it.

Classes: row 0; rows 1-25 (one semantic decoder); row 26; rows 27-30 (one
opening decoder); row 31; row 32. Within the two multi-row classes the charge
is the class maximum because the decoders do not expose which row they
decoded (optional tightening: a lemma that the parsed record count equals the
address label row).

The proof is a new dispatcher, a copy of `UnifiedDecoderBound.component_bound`
whose per-component bound only has to hold for rows of the component's class,
followed by copies of the three thin wrappers. No R1 file changes. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.RowCharge
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 AspisR1.TranscriptView
open CanonicalAddressEmbedding

/-! ## Classes and caps -/

/-- Class representative of a decoder component (row). -/
def cls (n : Nat) : Nat :=
  if n = 0 then 0 else if n < 26 then 1 else if n = 26 then 26
  else if n < 31 then 27 else if n = 31 then 31 else if n = 32 then 32 else 33

theorem cls_sem (k : Nat) (h0 : 0 < k) (h : k < 26) : cls k = 1 := by
  unfold cls; rw [if_neg (by omega), if_pos h]

theorem cls_open (k : Nat) (hlo : 27 ≤ k) (hhi : k < 31) : cls k = 27 := by
  unfold cls
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hhi]

/-- The cap of a class: the classifier budget for the one-row classes, the
row-1 budget (the largest of rows 1-25) for the semantic class, R1's
`openingCap` (the sum of the four opening budgets) for rows 27-30, and 0 for
addresses that no component decodes. Depends on `n` only through `cls n`. -/
def classCap (n : Nat) : ℚ :=
  if cls n = 1 then LiteralClassifier.budget 1
  else if cls n = 27 then OpeningSamplerBound.openingCap
  else if cls n = 33 then 0
  else LiteralClassifier.budget (cls n)

theorem classCap_congr (i n : Nat) (h : cls i = cls n) : classCap i = classCap n := by
  unfold classCap; rw [h]

private theorem atom_nonneg : 0 ≤ SemanticBudget.atom := by
  unfold SemanticBudget.atom R0P.SemSource.deltaQ
  positivity

private theorem sem_le (i : Nat) (h0 : i ≠ 0) (hs : i < 26) :
    LiteralClassifier.budget i ≤ LiteralClassifier.budget 1 := by
  have h1 : LiteralClassifier.budget 1 = (54400 : ℚ) * SemanticBudget.atom := by
    have h := SemanticBudget.budget_eq ⟨1, by decide⟩
    simp only [LiteralClassifier.budget, show (1 : Nat) < 25 by decide, if_true]
    rw [h]
    norm_num [SemanticBudget.roots]
  rw [h1]
  by_cases h25 : i < 25
  · simp only [LiteralClassifier.budget, if_pos h25]
    rw [SemanticBudget.budget_eq ⟨i, h25⟩]
    have hr : (SemanticBudget.roots ⟨i, h25⟩ : ℚ) ≤ 54400 := by
      have : SemanticBudget.roots ⟨i, h25⟩ ≤ 54400 := by
        unfold SemanticBudget.roots
        split_ifs with ha <;> first | omega | exact absurd ha h0
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hr atom_nonneg
  · have hi : i = 25 := by omega
    subst hi
    have he : LiteralClassifier.budget 25 = SemanticBudget.atom := by
      simp only [LiteralClassifier.budget, show ¬ ((25 : Nat) < 25) by omega, if_false]
      rfl
    rw [he]
    have := atom_nonneg
    linarith

private theorem opening_parts :
    OpeningSamplerBound.openingCap = LiteralOpeningDensity.gammaBudget +
      LiteralOpeningDensity.kappaBudget + 2 * LiteralOpeningDensity.foldBudget := by
  unfold OpeningSamplerBound.openingCap LiteralOpeningDensity.gammaBudget
    LiteralOpeningDensity.kappaBudget LiteralOpeningDensity.foldBudget
  ring

private theorem open_le (i : Nat) (hlo : 27 ≤ i) (hhi : i < 31) :
    LiteralClassifier.budget i ≤ OpeningSamplerBound.openingCap := by
  have hg := LiteralOpeningDensity.gammaBudget_nonneg
  have hk := LiteralOpeningDensity.kappaBudget_nonneg
  have hf := LiteralOpeningDensity.foldBudget_nonneg
  rw [opening_parts]
  have hc : i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · have he : LiteralClassifier.budget 27 = LiteralOpeningDensity.gammaBudget := by
      simp only [LiteralClassifier.budget, show ¬ ((27 : Nat) < 25) by omega, if_false]
    rw [he]; linarith
  · have he : LiteralClassifier.budget 28 = LiteralOpeningDensity.kappaBudget := by
      simp only [LiteralClassifier.budget, show ¬ ((28 : Nat) < 25) by omega, if_false]
    rw [he]; linarith
  · have he : LiteralClassifier.budget 29 = LiteralOpeningDensity.foldBudget := by
      simp only [LiteralClassifier.budget, show ¬ ((29 : Nat) < 25) by omega, if_false]
    rw [he]; linarith
  · have he : LiteralClassifier.budget 30 = LiteralOpeningDensity.foldBudget := by
      simp only [LiteralClassifier.budget, show ¬ ((30 : Nat) < 25) by omega, if_false]
    rw [he]; linarith

theorem classCap_of_one (n : Nat) (h : cls n = 1) :
    classCap n = LiteralClassifier.budget 1 := by
  unfold classCap; rw [h, if_pos rfl]

theorem classCap_of_27 (n : Nat) (h : cls n = 27) :
    classCap n = OpeningSamplerBound.openingCap := by
  unfold classCap; rw [h, if_neg (by omega), if_pos rfl]

theorem classCap_of_single (n k : Nat) (h : cls n = k) (h1 : k ≠ 1) (h27 : k ≠ 27)
    (h33 : k ≠ 33) : classCap n = LiteralClassifier.budget k := by
  unfold classCap; rw [h, if_neg h1, if_neg h27, if_neg h33]

/-- Every row's budget is at most its own class cap. -/
theorem budget_le_own (i : Nat) (hi : i < 33) : LiteralClassifier.budget i ≤ classCap i := by
  by_cases h0 : i = 0
  · subst h0
    have hc : cls 0 = 0 := by unfold cls; rw [if_pos rfl]
    rw [classCap_of_single 0 0 hc (by omega) (by omega) (by omega)]
  by_cases hs : i < 26
  · rw [classCap_of_one i (cls_sem i (by omega) hs)]
    exact sem_le i h0 hs
  by_cases h26 : i = 26
  · subst h26
    have hc : cls 26 = 26 := by
      unfold cls; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    rw [classCap_of_single 26 26 hc (by omega) (by omega) (by omega)]
  by_cases ho : i < 31
  · rw [classCap_of_27 i (cls_open i (by omega) ho)]
    exact open_le i (by omega) ho
  have hc : i = 31 ∨ i = 32 := by omega
  rcases hc with rfl | rfl
  · have hc : cls 31 = 31 := by
      unfold cls
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    rw [classCap_of_single 31 31 hc (by omega) (by omega) (by omega)]
  · have hc : cls 32 = 32 := by
      unfold cls
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl]
    rw [classCap_of_single 32 32 hc (by omega) (by omega) (by omega)]

theorem budget_le_classCap (i n : Nat) (hi : i < 33) (h : cls i = cls n) :
    LiteralClassifier.budget i ≤ classCap n :=
  (budget_le_own i hi).trans (le_of_eq (classCap_congr i n h))

/-! ## The row an address dispatches to -/

variable {M Cv : Type} {L : Nat}

/-- The component `UnifiedDecoder.decode` dispatches the address to, as a
function of the address and the selected public statement (33: none). -/
def rowOf (pub : UnifiedSampler.Public L) (a : Addr L) : Nat :=
  if (PublicInitParse.parse pub.pubBytes a).isSome then 0
  else match parseAbsorb a with
    | some (_, label, _) => UnifiedLabels.row label
    | none => 33

theorem decode_component (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.decode p hD pub a T = some (own, pend, g)) :
    rowOf pub a < 33 ∧ UnifiedDecoder.component p hD pub (rowOf pub a) a T = some (own, pend, g) := by
  unfold UnifiedDecoder.decode at hd
  unfold rowOf
  by_cases hinit : (PublicInitParse.parse pub.pubBytes a).isSome
  · simp only [if_pos hinit] at hd ⊢
    exact ⟨by omega, hd⟩
  · simp only [if_neg hinit] at hd ⊢
    cases hp : parseAbsorb a with
    | none => simp [hp] at hd
    | some parsed =>
        rcases parsed with ⟨endpoint, label, data⟩
        simp only [hp, Option.bind_some] at hd
        dsimp only
        refine ⟨?_, hd⟩
        by_contra hnot
        rw [UnifiedDecoder.component_none p hD pub _ (by omega)] at hd
        simp at hd

/-! ## Class-restricted dispatch (copy of `UnifiedDecoderBound.component_bound`) -/

theorem component_bound_class (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hn : n < 33)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hcomponent : UnifiedDecoder.component p hD pub n a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i → cls i = cls n →
        independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P, m, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  by_cases h0 : n = 0
  · subst n
    rw [UnifiedDecoder.component_initial] at hcomponent
    obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
      DecoderStateList.lift_sound (UnifiedInitialDecoder.decode p hD pub) a T
        own pend g hcomponent
    have hfixed₀ : ∀ c1,
        PublicInitParse.parse pub.pubBytes a = some c1 →
          independentMean
            (UnifiedSampler.samp p hD 0 (emptyPrefix pub) (.initial c1)).toProgram
            (fun w => obs (emptyPrefix pub, .initial c1, w.2)) ≤ B := by
      intro c1 hc1
      exact hfixed 0 (emptyPrefix pub) (.initial c1) (by omega) (by rfl) rfl
    have hbound := UnifiedInitialLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
      hdecode obs B hfixed₀
    cases heq
    rw [DecoderStateList.lifted_law]
    exact hbound
  · by_cases hsem : n < 26
    · have hnlo : 0 < n := by omega
      rw [UnifiedDecoder.component_semantic p hD pub n hnlo hsem] at hcomponent
      obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
        DecoderStateList.lift_sound (UnifiedSemanticDecoder.decode p pub) a T
          own pend g hcomponent
      have hfixed_sem : ∀ ctx,
          UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx →
          0 < ctx.records.length → ctx.records.length < 26 →
          ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
            independentMean
              (UnifiedSampler.samp p hD ctx.records.length
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
              (fun w => obs
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
        intro ctx hp hlo hhi as has
        have hround :
            (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
          simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
            PrefixRecordLength.fromAnswers_length]
        exact hfixed ctx.records.length
          (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
          (by omega) hround ((cls_sem _ hlo hhi).trans (cls_sem n hnlo hsem).symm)
      have hbound := UnifiedSemanticLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
        hdecode obs B hfixed_sem
      cases heq
      rw [DecoderStateList.lifted_law]
      exact hbound
    · by_cases h26 : n = 26
      · subst n
        rw [UnifiedDecoder.component_reseed] at hcomponent
        obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
          DecoderStateList.lift_sound (UnifiedReseedDecoder.decode p pub) a T
            own pend g hcomponent
        have hfixed_reseed : ∀ ctx,
            UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx →
            ctx.records.length = 26 →
            ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
              independentMean
                (UnifiedSampler.samp p hD 26
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
                (fun w => obs
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
          intro ctx hp hlen as has
          have hround :
              (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
            simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
              PrefixRecordLength.fromAnswers_length]
          exact hfixed 26 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
            (.payload ctx.message) (by decide) (by omega) rfl
        have hbound := UnifiedReseedLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
          hdecode obs B hfixed_reseed
        cases heq
        rw [DecoderStateList.lifted_law]
        exact hbound
      · by_cases h31 : n = 31
        · subst n
          rw [UnifiedDecoder.component_query] at hcomponent
          exact UnifiedQueryLaw.decoded_bound p hD pub a T own pend g hcomponent obs B
            (by
              intro ctx hp hlen as has
              have hround :
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = 31 := by
                simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
                  PrefixRecordLength.fromAnswers_length, hlen]
              exact hfixed 31 (UnifiedSemanticLaw.mkPrefix p pub T ctx as)
                (.payload ctx.message) (by decide) hround rfl)
        · by_cases hrho : n = 32
          · subst n
            rw [UnifiedDecoder.component_rho] at hcomponent
            obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
              DecoderStateList.lift_sound (JointUnifiedDecoder.decode p pub 27 4) a T
                own pend g hcomponent
            have hfixed_rho : ∀ ctx,
                JointContext.parse p pub.pubBytes pub.tag 27 4 a T = some ctx →
                ctx.records.length = 31 →
                ∀ as, as.length =
                    (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length →
                  independentMean
                    (UnifiedSampler.samp p hD 32
                      (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                        (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as))
                      (.payload ctx.nextMessage)).toProgram
                    (fun w => obs
                      (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                        (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as),
                        .payload ctx.nextMessage, w.2)) ≤ B := by
              intro ctx hp hlen as has
              have hround := JointTranscriptView.parsed_prefix_length p pub 27 4 a T
                ctx hp hlen as
              exact hfixed 32
                (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
                  (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as))
                (.payload ctx.nextMessage) (by decide) hround rfl
            have hbound := JointUnifiedBound.decoded_bound p hD pub 27 4 a T
              own₀ pend₀ g₀ hdecode obs B hfixed_rho
            cases heq
            rw [DecoderStateList.lifted_law]
            exact hbound
          · have hopening_lo : 27 ≤ n := by omega
            have hopening_hi : n < 31 := by omega
            rw [UnifiedDecoder.component_opening p hD pub n hopening_lo hopening_hi]
              at hcomponent
            obtain ⟨own₀, pend₀, g₀, hdecode, heq⟩ :=
              DecoderStateList.lift_sound (UnifiedOpeningDecoder.decode p pub) a T
                own pend g hcomponent
            have hfixed_opening : ∀ ctx,
                UnifiedOpeningDecoder.parse p pub a T = some ctx →
                27 ≤ ctx.records.length → ctx.records.length < 31 →
                ∀ as, as.length = (PrefixAnswers.missing p T ctx.records).length →
                  independentMean
                    (UnifiedSampler.samp p hD ctx.records.length
                      (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)).toProgram
                    (fun w => obs
                      (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message, w.2)) ≤ B := by
              intro ctx hp hlo hhi as has
              have hround :
                  (UnifiedSemanticLaw.mkPrefix p pub T ctx as).rounds.length = ctx.records.length := by
                simp [UnifiedSemanticLaw.mkPrefix, TranscriptView.ordinary_length,
                  PrefixRecordLength.fromAnswers_length]
              exact hfixed ctx.records.length
                (UnifiedSemanticLaw.mkPrefix p pub T ctx as) (.payload ctx.message)
                (by omega) hround
                ((cls_open _ hlo hhi).trans (cls_open n hopening_lo hopening_hi).symm)
            have hbound := UnifiedOpeningLaw.decoded_bound p hD pub a T own₀ pend₀ g₀
              hdecode obs B hfixed_opening
            cases heq
            rw [DecoderStateList.lifted_law]
            exact hbound

/-- Unified decoder, class-restricted (refines `UnifiedDecoderBound.decoded_bound`). -/
theorem decoded_bound_class (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : UnifiedDecoder.decode p hD pub a T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i → cls i = cls (rowOf pub a) →
        independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P, m, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨hn, hcomponent⟩ := decode_component p hD pub a T own pend g hd
  exact component_bound_class p hD pub (rowOf pub a) hn a T own pend g hcomponent obs B hfixed

/-- The row of a raw byte address: its canonical address's row, 33 if none. -/
def rawRow (pub : UnifiedSampler.Public L) (a : Bytes) : Nat :=
  match CanonicalRawTrace.decode L a with
  | some ac => rowOf pub ac.val
  | none => 33

/-- Raw decoder, class-restricted (refines `RawUnifiedDecoder.decoded_bound`). -/
theorem raw_decoded_bound_class (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Bytes) (T : Table Bytes State)
    (s : BS Bytes State (List State)) (ps : List (Bytes × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : RawUnifiedDecoder.decode p hD pub a T = some (s, ps, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M),
      i < 33 → P.rounds.length = i → cls i = cls (rawRow pub a) →
        independentMean (UnifiedSampler.samp p hD i P m).toProgram
          (fun w => obs (P, m, w.2)) ≤ B) : blaw g obs s ps ≤ B := by
  unfold RawUnifiedDecoder.decode at hd
  cases ha : CanonicalRawTrace.decode L a with
  | none => simp [ha] at hd
  | some ac =>
      simp only [ha, Option.bind_some] at hd
      have hrow : rawRow pub a = rowOf pub ac.val := by simp [rawRow, ha]
      cases hc : UnifiedDecoder.decode p hD pub ac.val (RawBoundedTrace.table L T) with
      | none => rw [RawUnifiedDecoder.atCanonical_none p hD pub ac T hc] at hd; cases hd
      | some result =>
          rcases result with ⟨bs, bp, bg⟩
          rw [RawUnifiedDecoder.atCanonical_of_decode p hD pub ac T bs bp bg hc] at hd
          have hb := decoded_bound_class p hD pub ac.val
            (RawBoundedTrace.table L T) bs bp bg hc obs B
            (fun i P m hi hr hcl => hfixed i P m hi hr (hcl.trans (by rw [hrow])))
          cases hd
          rw [RawBackgroundCompletion.blaw_eq]
          exact hb

/-! ## The literal classifier -/

open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript RawLiteralDecoderDensity

/-- Literal decoder: each start's classifier mass is at most its class cap
(refines `RawAdaptiveClassifierHitDensity.literal_decoded_classifier_le`). -/
theorem literal_decoded_classifier_le_class
    (choose : WordChoice) (pub : LiteralTranscript.Public)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawLiteralDecoderDensity.decode choose pub a T = some (own, pend, g)) :
    blaw g (fun out => indicator (RawAdaptiveClassifierHitDensity.classifier out.1 out.2.1 T out.2.2))
      own pend ≤ classCap (rawRow pub a) := by
  unfold RawLiteralDecoderDensity.decode at hd
  cases hc : RawUnifiedDecoder.decode SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T with
  | none => simp [hc] at hd
  | some result =>
    rcases result with ⟨bs, bp, bg⟩
    simp only [hc, Option.map_some] at hd
    have hbound : blaw bg (fun out => indicator
        (RawAdaptiveClassifierHitDensity.classifier (restore (choose a T) out).1
          (restore (choose a T) out).2.1 T (restore (choose a T) out).2.2)) bs bp ≤
        classCap (rawRow pub a) := by
      refine raw_decoded_bound_class SelectedTranscriptParams.params
        (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        pub a T bs bp bg hc _ (classCap (rawRow pub a)) ?_
      intro i P m hi hround hcls
      subst i
      exact (LiteralDecoderEnrichment.density (choose a T P m) P m hi).trans
        (budget_le_classCap P.round (rawRow pub a) hi hcls)
    cases hd
    rw [BackgroundLawMap.blaw_map]
    exact hbound

/-- Piece (b): the charge of a decoded start, a function of the address and
the pre-read table only. -/
def charge (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (a : Bytes)
    (T : Table Bytes State) : ℚ :=
  match pubChoice a T with
  | some pub => classCap (rawRow pub a)
  | none => 0

/-- Piece (b) (refines `RawAdaptiveClassifierHitDensity.adaptive_decoded_classifier_le`). -/
theorem adaptive_decoded_classifier_le_charge
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (words : WordChoice)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own, pend, g)) :
    blaw g (fun out => indicator (RawAdaptiveClassifierHitDensity.classifier out.1 out.2.1 T out.2.2))
      own pend ≤ charge pubChoice a T := by
  unfold RawAdaptiveLiteralDecoder.decode at hd
  cases hp : pubChoice a T with
  | none => simp [hp] at hd
  | some pub =>
    simp only [hp, Option.bind_some] at hd
    simp only [charge, hp]
    exact literal_decoded_classifier_le_class words pub a T own pend g hd

/-! ## Check against R1 -/

/-- Every class cap is at most the common envelope. -/
theorem classCap_le_B (n : Nat) : classCap n ≤ PerAttemptEnvelope.B := by
  have hB : 0 ≤ PerAttemptEnvelope.B := by unfold PerAttemptEnvelope.B; positivity
  unfold classCap
  split_ifs with h1 h27 h33
  · exact LiteralBudgetEnvelope.row_le 1 (by decide)
  · exact PerAttemptEnvelope.opening_cap_le
  · exact hB
  · apply LiteralBudgetEnvelope.row_le
    unfold cls at h1 h27 h33 ⊢
    split_ifs at h1 h27 h33 ⊢ <;> omega

theorem charge_le_B (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (a : Bytes)
    (T : Table Bytes State) : charge pubChoice a T ≤ PerAttemptEnvelope.B := by
  unfold charge
  split
  · exact classCap_le_B _
  · unfold PerAttemptEnvelope.B; positivity

/-- R1's uniform statement recovered from piece (b). -/
theorem adaptive_decoded_classifier_le_via_charge
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice) (words : WordChoice)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own, pend, g)) :
    blaw g (fun out => indicator (RawAdaptiveClassifierHitDensity.classifier out.1 out.2.1 T out.2.2))
      own pend ≤ PerAttemptEnvelope.B :=
  (adaptive_decoded_classifier_le_charge pubChoice words a T own pend g hd).trans
    (charge_le_B pubChoice a T)

#print axioms budget_le_classCap
#print axioms decode_component
#print axioms component_bound_class
#print axioms raw_decoded_bound_class
#print axioms literal_decoded_classifier_le_class
#print axioms adaptive_decoded_classifier_le_charge
#print axioms classCap_le_B
#print axioms adaptive_decoded_classifier_le_via_charge
end AspisPerStep.RowCharge
end
