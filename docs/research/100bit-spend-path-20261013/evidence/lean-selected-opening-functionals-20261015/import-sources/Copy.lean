import R0P.CopyConstants
import R0P.CoreExt
import R0P.Path

/-! G4 literal explicit-input Copy terminal helpers, source T =
crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs, C = its
_constants.rs, pinned e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.

The original Core.Family input gap is resolved by the lead's CoreExt.CFamily:
CHolds supplies this trace's H1 = A26(b), with lambda/chi explicit parameters.
The literal explicit-input functions below are preserved; the continuation
proves their complete row equations and identifies the two aggregate helper
sums. No LogUp-to-tuple-equality implication is asserted. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- T:137–141: high/low tensor factors of the row selectors. -/
structure CopySelectors (K : Type) where
  high : Fin 64 → K
  low : Fin 16 → K

/-- T:173–177, Selectors.row. Division and remainder are the source's
row >> 4 and row & 15 on the bounded generated rows. -/
def copySelectorRow (s : CopySelectors K) (r : Fin 1024) : K :=
  s.high ⟨r.val / 16, by omega⟩ * s.low ⟨r.val % 16, Nat.mod_lt _ (by omega)⟩

/-- T:118–135, selector_mask_sum_16. The set bits are visited in increasing
order, exactly the repeated trailing-zero extraction and clearing loop.
The 16-bit complement retains the source subtraction order. -/
def copySelectorMaskSum16 (values : Fin 16 → K) (mask : Nat) : K :=
  let bits := List.ofFn (fun i : Fin 16 => i)
  let complement := (bits.filter (fun i => mask.testBit i.val)).length > 8
  let selectedMask := if complement then mask ^^^ 65535 else mask
  (bits.filter (fun i => selectedMask.testBit i.val)).foldl
    (fun sum i => if complement then sum - values i else sum + values i)
    (if complement then 1 else 0)

/-- T:179–191, active_literal, the production non-active-mask-basis-audit path. -/
def copyActiveLiteral (s : CopySelectors K) : K :=
  (List.ofFn (fun block : Fin 64 => block)).foldl (fun sum block =>
    let mask := copyActiveRowMasks block
    if mask ≠ 0 then sum + s.high block * copySelectorMaskSum16 s.low mask else sum) 0

/-- T:237–244: the powers array, retaining the iterative multiply by lambda. -/
def copyPowers (lambda : K) (i : Fin 16) : K :=
  (List.range i.val).foldl (fun power _ => power * lambda) lambda

/-- T:248–256, C:10–25: sixteen pattern cells before lambda compression.
Kinds other than 1 emit zero, as in the initialized source accumulator. -/
def copyPatternTuple (pattern : CopyPattern) (openings : Fin 16 → K) : Fin 16 → K :=
  fun limb => if pattern.kinds limb = 1 then
    openings (pattern.columns limb) + (pattern.offsets limb : K) else 0

/-- T:232–263, pattern_values_literal. This is the production
non-pattern-window-audit path, preserving limb and accumulation order. -/
def copyPatternValuesLiteral (openings : Fin 16 → K) (lambda : K) : Fin 14 → K :=
  let powers := copyPowers lambda
  fun patternIndex =>
    let pattern := copyPatterns patternIndex
    (List.ofFn (fun limb : Fin 16 => limb)).foldl (fun value limb =>
      if pattern.kinds limb = 1 then
        let source := openings (pattern.columns limb) + (pattern.offsets limb : K)
        value + powers limb * source
      else value) 0

/-- T:359–377, link_weight. A generated link has weight_kind in 0..4;
the source's unreachable default is impossible for the bounded descriptor. -/
def copyLinkWeight (link : CopyLink) (appendIndex : Nat) (variant : Variant) : K :=
  match link.weightKind.val with
  | 0 => 1
  | 1 => if variant = .privateTransfer then 1 else 0
  | 2 => if variant = .withdrawal then 1 else 0
  | 3 => ((1 - ((appendIndex >>> link.weightLevel) &&& 1) : Nat) : K)
  | _ => (((appendIndex >>> link.weightLevel) &&& 1 : Nat) : K)

/-- T:79–103,248–255,448–449: the tagged endpoint tuple is the literal tag
followed by the pattern's 16 row-local cells (with offsets and zero lanes). -/
def copyEndpointTuple (A : Trace K) (tag : Nat) (endpoint : CopyEndpoint) : K × (Fin 16 → K) :=
  ((tag : K), copyPatternTuple (copyPatterns endpoint.pattern)
    (fun c => A (Fin.castLE (by omega) c) endpoint.row))

/-- T:95–103, C:27–164: producer tuple for any generated link. -/
def copyProducerTuple (A : Trace K) (link : CopyLink) : K × (Fin 16 → K) :=
  copyEndpointTuple A link.tag link.producer

/-- T:95–103, C:27–164: consumer tuple for any generated link. -/
def copyConsumerTuple (A : Trace K) (link : CopyLink) : K × (Fin 16 → K) :=
  copyEndpointTuple A link.tag link.consumer

/-- T:331–337, CopyRowExtension. -/
structure CopyRowExtension (K : Type) where
  producerValues : Fin 2 → K
  producerWeights : Fin 2 → K
  consumerValues : Fin 2 → K
  consumerWeights : Fin 2 → K

/-- T:423–450, accumulate_endpoint, excluding selector-cache and binary-weight
rewrite audit paths. The source adds the weight before the tagged value. -/
def copyAccumulateEndpoint (values weights : Fin 2 → K) (endpoint : CopyEndpoint)
    (tag : Nat) (weight : K) (patterns : Fin 14 → K) (selectors : CopySelectors K) :
    (Fin 2 → K) × (Fin 2 → K) :=
  let selector := copySelectorRow selectors endpoint.row
  let slot := endpoint.slot
  let weights := Function.update weights slot (weights slot + selector * weight)
  let compressed := (tag : K) + patterns endpoint.pattern
  let values := Function.update values slot (values slot + selector * compressed)
  (values, weights)

/-- T:339–357, copy_residual. Parentheses and arithmetic order are literal. -/
def copyResidual (row : CopyRowExtension K) (helper chi : K) : K :=
  let denominators : Fin 4 → K :=
    ![chi - row.producerValues 0, chi - row.producerValues 1,
      chi - row.consumerValues 0, chi - row.consumerValues 1]
  let producerDenominator := denominators 0 * denominators 1
  let consumerDenominator := denominators 2 * denominators 3
  let producerNumerator := row.producerWeights 0 * denominators 1 +
    row.producerWeights 1 * denominators 0
  let consumerNumerator := row.consumerWeights 0 * denominators 3 +
    row.consumerWeights 1 * denominators 2
  producerDenominator * (helper * consumerDenominator + consumerNumerator) -
    consumerDenominator * producerNumerator

/-- T:910–972,1048,1068–1072, evaluate_with_selectors, all audit features off.
Returns (residual, active) and keeps H1/lambda/chi as explicit required inputs. -/
def copyEvaluateWithSelectors (openings : Fin 16 → K) (h1 : K)
    (selectors : CopySelectors K) (lambda chi : K) (appendIndex : Nat) (variant : Variant) : K × K :=
  let patterns := copyPatternValuesLiteral openings lambda
  let initial : CopyRowExtension K := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  let row := copyLinks.foldl (fun row link =>
    let weight := copyLinkWeight link appendIndex variant
    let producer := copyAccumulateEndpoint row.producerValues row.producerWeights
      link.producer link.tag weight patterns selectors
    let consumer := copyAccumulateEndpoint row.consumerValues row.consumerWeights
      link.consumer link.tag weight patterns selectors
    ⟨producer.1, producer.2, consumer.1, consumer.2⟩) initial
  let active := copyActiveLiteral selectors
  (active * copyResidual row h1 chi, active)

/-- T:359–377: a weight-kind-zero link is always enabled, without inspecting
any generated table or placing a condition on variant or append index. -/
theorem copy_linkWeight_zero (link : CopyLink) (h : link.weightKind = 0)
    (appendIndex : Nat) (variant : Variant) :
    copyLinkWeight (K := K) link appendIndex variant = 1 := by
  simp only [copyLinkWeight, h, Fin.val_zero]

/-- C:27–164: the sparse positivity block is part of the literal full registry.
The proof treats both large neighboring blocks abstractly. -/
theorem copy_positivity_mem (link : CopyLink) (h : link ∈ copyPositivityLinks) :
    link ∈ copyLinks := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

/-- C:17–20: the four singleton pattern formulas, proved symbolically.
Only sparse index dispatch is reduced; no vector or global table is evaluated. -/
theorem copy_singleton_patterns (openings : Fin 16 → K) :
    copyPatternTuple (copyPatterns 6) openings = (fun i => if i = 0 then openings 0 else 0) ∧
    copyPatternTuple (copyPatterns 7) openings = (fun i => if i = 0 then openings 10 else 0) ∧
    copyPatternTuple (copyPatterns 8) openings = (fun i => if i = 0 then openings 1 else 0) ∧
    copyPatternTuple (copyPatterns 9) openings = (fun i => if i = 0 then openings 2 else 0) := by
  have h76 : (7 : Fin 14) ≠ 6 := by omega
  have h86 : (8 : Fin 14) ≠ 6 := by omega
  have h87 : (8 : Fin 14) ≠ 7 := by omega
  have h96 : (9 : Fin 14) ≠ 6 := by omega
  have h97 : (9 : Fin 14) ≠ 7 := by omega
  have h98 : (9 : Fin 14) ≠ 8 := by omega
  simp only [copyPatterns, if_neg h76, if_neg h86, if_neg h87,
    if_neg h96, if_neg h97, if_neg h98]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> by_cases hi : i = 0
  all_goals simp only [copyPatternTuple, copyPattern6, copyPattern7, copyPattern8,
    copyPattern9, hi, if_true, if_false, Nat.cast_zero, add_zero, zero_ne_one]

/-- C:42–45: the exact four positivity links are entries of the generated
registry, weight one for every variant/index, and carry the stated single
trace cell with all fifteen padding limbs zero. No equality of endpoints is
claimed: this identifies data, not the later probabilistic LogUp argument. -/
theorem copy_positivity_links (pub : Public K) (A : Trace K) :
    (∀ link ∈ copyPositivityLinks, link ∈ copyLinks ∧
      copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1) ∧
    copyProducerTuple A copyPositivityLink0 =
      ((1124073486 : K), fun i => if i = 0 then A 10 1008 else 0) ∧
    copyConsumerTuple A copyPositivityLink0 =
      ((1124073486 : K), fun i => if i = 0 then A 0 1014 else 0) ∧
    copyProducerTuple A copyPositivityLink1 =
      ((1124073487 : K), fun i => if i = 0 then A 10 1010 else 0) ∧
    copyConsumerTuple A copyPositivityLink1 =
      ((1124073487 : K), fun i => if i = 0 then A 1 1014 else 0) ∧
    copyProducerTuple A copyPositivityLink2 =
      ((1124073488 : K), fun i => if i = 0 then A 10 1012 else 0) ∧
    copyConsumerTuple A copyPositivityLink2 =
      ((1124073488 : K), fun i => if i = 0 then A 1 1015 else 0) ∧
    copyProducerTuple A copyPositivityLink3 =
      ((1124073489 : K), fun i => if i = 0 then A 2 1014 else 0) ∧
    copyConsumerTuple A copyPositivityLink3 =
      ((1124073489 : K), fun i => if i = 0 then A 0 1015 else 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro link h
    refine ⟨copy_positivity_mem link h, ?_⟩
    apply copy_linkWeight_zero
    simp only [copyPositivityLinks, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  all_goals
    simp only [copyProducerTuple, copyConsumerTuple, copyEndpointTuple,
      copyPositivityLink0, copyPositivityLink1, copyPositivityLink2, copyPositivityLink3]
  · rw [(copy_singleton_patterns _).2.1]
    rfl
  · rw [(copy_singleton_patterns _).1]
    rfl
  · rw [(copy_singleton_patterns _).2.1]
    rfl
  · rw [(copy_singleton_patterns _).2.2.1]
    rfl
  · rw [(copy_singleton_patterns _).2.1]
    rfl
  · rw [(copy_singleton_patterns _).2.2.1]
    rfl
  · rw [(copy_singleton_patterns _).2.2.2]
    rfl
  · rw [(copy_singleton_patterns _).1]
    rfl

/-! ## G4 continuation: challenge-dependent literal family

CoreExt (lead decision dae112e8f) supplies H1 and the two challenges. The
high/low adapter is the already proved Boolean-row adapter from Path; no
identity for arbitrary off-domain selector inputs is asserted. -/
attribute [local irreducible] copyActiveRowMasks copyPatterns copyLinks
  copyLinksBeforePositivity copyLinksAfterPositivity

/-- T:137–176, the Boolean-row high/low selector adapter. -/
def copySelectors (sel : Sel K) : CopySelectors K := ⟨g2High sel, g2Low sel⟩

/-- T:910–972,1048,1068–1072, with all audit alternatives off.
CHolds supplies this same trace's A26(b), lambda and chi explicitly. -/
def copyFamily : CFamily K where
  residuals := fun pub lam chi o h1 sel =>
    [(copyEvaluateWithSelectors o.z h1 (copySelectors sel) lam chi
      pub.nextPairIndex pub.variant).1]

/-- T:179–191 and C:5: selected rows, without evaluating the mask table. -/
abbrev CopyActiveRow (b : Fin 1024) : Prop :=
  (copyActiveRowMasks ⟨b.val / 16, by omega⟩).testBit (b.val % 16) = true

/-- The literal inactive set read by the terminal's (1-active) coefficient. -/
def copyInactiveRows : Finset (Fin 1024) :=
  Finset.univ.filter (fun b => ¬ CopyActiveRow b)

private theorem copy_selector_row (b r : Fin 1024) :
    copySelectorRow (copySelectors (rowSel (K := K) b)) r = rowSel b r := by
  simp only [copySelectorRow, copySelectors, g2_high_row, g2_low_row, rowSel]
  by_cases hr : r = b
  · subst r; simp
  · have hpair : ¬ (r.val / 16 = b.val / 16 ∧ r.val % 16 = b.val % 16) := by
      intro h; apply hr; apply Fin.ext; omega
    by_cases hh : r.val / 16 = b.val / 16
    · have hl : r.val % 16 ≠ b.val % 16 := fun h => hpair ⟨hh,h⟩
      simp only [if_pos hh, if_neg hl, if_neg hr, mul_zero]
    · simp only [if_neg hh, if_neg hr, zero_mul]

private theorem copy_fold_add {α : Type} (xs : List α) (f : α → K) (a : K) :
    xs.foldl (fun acc x => acc + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

private theorem copy_signed_fold {α : Type} (xs : List α) (f : α → K)
    (c : Prop) [Decidable c] (a : K) :
    xs.foldl (fun acc x => if c then acc-f x else acc+f x) a =
      if c then a-(xs.map f).sum else a+(xs.map f).sum := by
  induction xs generalizing a with
  | nil => by_cases hc : c <;> simp [hc]
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hc : c <;> simp only [List.map_cons,
      List.sum_cons, hc, if_true, if_false] <;> ring

private theorem copy_indicator_sum {α : Type} [DecidableEq α] (xs : List α)
    (hn : xs.Nodup) (b : α) :
    (xs.map (fun x => if x = b then (1 : K) else 0)).sum =
      if b ∈ xs then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.nodup_cons.mp hn
    by_cases he : x = b
    · subst x
      simp [hx, ih ht]
    · by_cases hb : b ∈ xs <;> simp [he, Ne.symm he, hb, ih ht]

private theorem copy_mask_indicator (mask : Nat) (l : Fin 16) :
    copySelectorMaskSum16 (fun i => if i = l then (1 : K) else 0) mask =
      if mask.testBit l.val then 1 else 0 := by
  let bits := List.ofFn (fun i : Fin 16 => i)
  have hn : bits.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hm : l ∈ bits := List.mem_ofFn.mpr ⟨l,rfl⟩
  have hs (m : Nat) :
      ((bits.filter (fun i => m.testBit i.val)).map
        (fun i => if i = l then (1 : K) else 0)).sum =
        if m.testBit l.val then 1 else 0 := by
    rw [copy_indicator_sum _ (hn.filter _) l]
    simp only [List.mem_filter, hm, true_and]
  have ht : Nat.testBit 65535 l.val = true := by
    rw [show (65535 : Nat) = 2^16-1 from rfl, Nat.testBit_two_pow_sub_one]
    simp only [l.isLt, decide_true]
  change (bits.filter (fun i =>
    (if (bits.filter (fun i => mask.testBit i.val)).length > 8 then mask ^^^ 65535 else mask).testBit i.val)).foldl
    (fun acc i => if (bits.filter (fun i => mask.testBit i.val)).length > 8
      then acc-(if i = l then 1 else 0) else acc+(if i = l then 1 else 0))
    (if (bits.filter (fun i => mask.testBit i.val)).length > 8 then 1 else 0) = _
  rw [copy_signed_fold]
  by_cases hc : (bits.filter (fun i => mask.testBit i.val)).length > 8
  · simp only [if_pos hc]
    rw [hs, Nat.testBit_xor, ht]
    cases mask.testBit l.val <;> simp
  · simp only [if_neg hc, hs, zero_add]

private theorem copy_active_sum (s : CopySelectors K) :
    copyActiveLiteral s = ∑ block : Fin 64,
      if copyActiveRowMasks block ≠ 0 then
        s.high block * copySelectorMaskSum16 s.low (copyActiveRowMasks block) else 0 := by
  unfold copyActiveLiteral
  have he : (fun (sum : K) (block : Fin 64) =>
      if copyActiveRowMasks block ≠ 0 then
        sum + s.high block * copySelectorMaskSum16 s.low (copyActiveRowMasks block) else sum) =
      (fun sum block => sum + (if copyActiveRowMasks block ≠ 0 then
        s.high block * copySelectorMaskSum16 s.low (copyActiveRowMasks block) else 0)) := by
    funext sum block
    by_cases h : copyActiveRowMasks block ≠ 0 <;> simp [h]
  rw [he, copy_fold_add, zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

theorem copy_active_row (b : Fin 1024) :
    copyActiveLiteral (copySelectors (rowSel (K := K) b)) =
      if CopyActiveRow b then 1 else 0 := by
  let h : Fin 64 := ⟨b.val / 16, by omega⟩
  let l : Fin 16 := ⟨b.val % 16, Nat.mod_lt _ (by omega)⟩
  have hl : g2Low (rowSel (K := K) b) = fun i => if i = l then 1 else 0 := by
    funext i
    rw [g2_low_row]
    simp only [Fin.ext_iff, l]
  rw [copy_active_sum, Finset.sum_eq_single h]
  · change (if copyActiveRowMasks h ≠ 0 then
      g2High (rowSel b) h * copySelectorMaskSum16 (g2Low (rowSel b)) (copyActiveRowMasks h) else 0) = _
    rw [g2_high_row, if_pos (show h.val = b.val/16 from rfl), one_mul,
      hl, copy_mask_indicator]
    by_cases hm : copyActiveRowMasks h = 0
    · simp [hm, CopyActiveRow, h]
    · rw [if_pos hm]
  · intro i _ hi
    have he : i.val ≠ b.val/16 := by
      intro he; apply hi; apply Fin.ext; exact he
    change (if copyActiveRowMasks i ≠ 0 then
      g2High (rowSel b) i * copySelectorMaskSum16 (g2Low (rowSel b)) (copyActiveRowMasks i) else 0) = 0
    rw [g2_high_row, if_neg he, zero_mul]
    split_ifs <;> rfl
  · simp


private theorem copy_power_fold (lam a : K) (n : Nat) :
    (List.range n).foldl (fun power _ => power * lam) a = a * lam^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, pow_succ, mul_assoc]

theorem copy_powers_eq (lam : K) (i : Fin 16) : copyPowers lam i = lam^(i.val+1) := by
  rw [copyPowers, copy_power_fold, pow_succ']

private theorem copy_pattern_fold (pattern : CopyPattern) (openings : Fin 16 → K)
    (lam : K) (xs : List (Fin 16)) (a : K) :
    xs.foldl (fun value limb => if pattern.kinds limb = 1 then
      value + copyPowers lam limb * (openings (pattern.columns limb) + (pattern.offsets limb : K))
      else value) a =
      a + (xs.map (fun limb => lam^(limb.val+1) * copyPatternTuple pattern openings limb)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hk : pattern.kinds i = 1 <;>
      simp [List.map_cons, List.sum_cons, copyPatternTuple, hk, copy_powers_eq, add_assoc]

theorem copy_pattern_values_eq (openings : Fin 16 → K) (lam : K) (p : Fin 14) :
    copyPatternValuesLiteral openings lam p =
      ∑ i : Fin 16, lam^(i.val+1) * copyPatternTuple (copyPatterns p) openings i := by
  simp only [copyPatternValuesLiteral, copy_pattern_fold, zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Row-equation notation for a source tagged tuple; only lemmas convert the
literal power/pattern loops to this sum. No tuple equality is asserted. -/
abbrev copyTupleValue (lam : K) (tuple : K × (Fin 16 → K)) : K :=
  tuple.1 + ∑ i : Fin 16, lam^(i.val+1) * tuple.2 i

private theorem copy_endpoint_value (A : Trace K) (lam : K) (tag : Nat) (ep : CopyEndpoint) :
    (tag : K) + copyPatternValuesLiteral (rowOpenings A ep.row).z lam ep.pattern =
      copyTupleValue lam (copyEndpointTuple A tag ep) := by
  rw [copy_pattern_values_eq]
  rfl

private theorem copy_selected_endpoint_value (A : Trace K) (lam : K)
    (tag : Nat) (ep : CopyEndpoint) (b : Fin 1024) :
    rowSel b ep.row * ((tag : K) + copyPatternValuesLiteral (rowOpenings A b).z lam ep.pattern) =
      if ep.row = b then copyTupleValue lam (copyEndpointTuple A tag ep) else 0 := by
  by_cases hb : ep.row = b
  · subst b
    rw [rowSel_self, one_mul, if_pos rfl, copy_endpoint_value]
  · rw [rowSel_ne b ep.row hb, zero_mul, if_neg hb]

private theorem copy_accumulate_values (values weights : Fin 2 → K) (ep : CopyEndpoint)
    (tag : Nat) (weight : K) (patterns : Fin 14 → K) (s : CopySelectors K) (slot : Fin 2) :
    (copyAccumulateEndpoint values weights ep tag weight patterns s).1 slot =
      values slot + if ep.slot = slot then copySelectorRow s ep.row * ((tag : K) + patterns ep.pattern) else 0 := by
  by_cases h : ep.slot = slot
  · subst slot
    simp only [copyAccumulateEndpoint, Function.update_self, if_true]
  · simp only [copyAccumulateEndpoint, Function.update_of_ne (Ne.symm h), if_neg h, add_zero]

private theorem copy_accumulate_weights (values weights : Fin 2 → K) (ep : CopyEndpoint)
    (tag : Nat) (weight : K) (patterns : Fin 14 → K) (s : CopySelectors K) (slot : Fin 2) :
    (copyAccumulateEndpoint values weights ep tag weight patterns s).2 slot =
      weights slot + if ep.slot = slot then copySelectorRow s ep.row * weight else 0 := by
  by_cases h : ep.slot = slot
  · subst slot
    simp only [copyAccumulateEndpoint, Function.update_self, if_true]
  · simp only [copyAccumulateEndpoint, Function.update_of_ne (Ne.symm h), if_neg h, add_zero]

private theorem copy_fold_project {α β : Type} (xs : List α) (step : β → α → β)
    (proj : β → K) (f : α → K) (hs : ∀ a x, proj (step a x) = proj a + f x) (a : β) :
    proj (xs.foldl step a) = proj a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, hs, List.map_cons, List.sum_cons, add_assoc]


/-- T:953–970, one literal producer-then-consumer loop iteration.
This names the identical step in copyEvaluateWithSelectors for its proof. -/
def copyAccumulateRow (pub : Public K) (patterns : Fin 14 → K) (s : CopySelectors K)
    (row : CopyRowExtension K) (link : CopyLink) : CopyRowExtension K :=
  let weight := copyLinkWeight link pub.nextPairIndex pub.variant
  let producer := copyAccumulateEndpoint row.producerValues row.producerWeights
    link.producer link.tag weight patterns s
  let consumer := copyAccumulateEndpoint row.consumerValues row.consumerWeights
    link.consumer link.tag weight patterns s
  ⟨producer.1, producer.2, consumer.1, consumer.2⟩

/-- Row-equation notation: source-order sum over all endpoints in a slot.
The list retains multiplicity. No assumption of one link per slot is made. -/
abbrev copyRowValues (A : Trace K) (lam : K) (b : Fin 1024)
    (endpoint : CopyLink → CopyEndpoint) (slot : Fin 2) : K :=
  (copyLinks.map (fun link => if (endpoint link).row = b ∧ (endpoint link).slot = slot then
    copyTupleValue lam (copyEndpointTuple A link.tag (endpoint link)) else 0)).sum

/-- Row-equation notation for the weights accumulated at that same slot. -/
abbrev copyRowWeights (pub : Public K) (b : Fin 1024)
    (endpoint : CopyLink → CopyEndpoint) (slot : Fin 2) : K :=
  (copyLinks.map (fun link => if (endpoint link).row = b ∧ (endpoint link).slot = slot then
    copyLinkWeight link pub.nextPairIndex pub.variant else 0)).sum

/-- Complete row catalogue, only used after proving literal-loop correspondence. -/
abbrev copyRowsAt (pub : Public K) (lam : K) (A : Trace K) (b : Fin 1024) : CopyRowExtension K :=
  ⟨copyRowValues A lam b CopyLink.producer, copyRowWeights pub b CopyLink.producer,
    copyRowValues A lam b CopyLink.consumer, copyRowWeights pub b CopyLink.consumer⟩

private theorem copy_fold_producer_values (xs : List CopyLink) (pub : Public K) (lam : K)
    (A : Trace K) (b : Fin 1024) (initial : CopyRowExtension K) (slot : Fin 2) :
    (xs.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) initial).producerValues slot =
      initial.producerValues slot + (xs.map (fun link =>
        if link.producer.row = b ∧ link.producer.slot = slot then copyTupleValue lam (copyEndpointTuple A link.tag link.producer) else 0)).sum := by
  refine copy_fold_project xs
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) (fun row => row.producerValues slot)
    (fun link => if link.producer.row = b ∧ link.producer.slot = slot then
      copyTupleValue lam (copyEndpointTuple A link.tag link.producer) else 0) ?_ initial
  intro row link
  change (copyAccumulateEndpoint row.producerValues row.producerWeights link.producer link.tag
    (copyLinkWeight link pub.nextPairIndex pub.variant)
    (copyPatternValuesLiteral (rowOpenings A b).z lam) (copySelectors (rowSel b))).1 slot = _
  rw [copy_accumulate_values, copy_selector_row, copy_selected_endpoint_value]
  by_cases hr : link.producer.row = b <;> by_cases hs : link.producer.slot = slot <;>
    simp [hr, hs]

private theorem copy_fold_producer_weights (xs : List CopyLink) (pub : Public K) (lam : K)
    (A : Trace K) (b : Fin 1024) (initial : CopyRowExtension K) (slot : Fin 2) :
    (xs.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) initial).producerWeights slot =
      initial.producerWeights slot + (xs.map (fun link =>
        if link.producer.row = b ∧ link.producer.slot = slot then copyLinkWeight link pub.nextPairIndex pub.variant else 0)).sum := by
  refine copy_fold_project xs
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) (fun row => row.producerWeights slot)
    (fun link => if link.producer.row = b ∧ link.producer.slot = slot then
      copyLinkWeight link pub.nextPairIndex pub.variant else 0) ?_ initial
  intro row link
  change (copyAccumulateEndpoint row.producerValues row.producerWeights link.producer link.tag
    (copyLinkWeight link pub.nextPairIndex pub.variant)
    (copyPatternValuesLiteral (rowOpenings A b).z lam) (copySelectors (rowSel b))).2 slot = _
  rw [copy_accumulate_weights, copy_selector_row]
  by_cases hr : link.producer.row = b <;> by_cases hs : link.producer.slot = slot <;>
    simp [hr, hs, rowSel]

private theorem copy_fold_consumer_values (xs : List CopyLink) (pub : Public K) (lam : K)
    (A : Trace K) (b : Fin 1024) (initial : CopyRowExtension K) (slot : Fin 2) :
    (xs.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) initial).consumerValues slot =
      initial.consumerValues slot + (xs.map (fun link =>
        if link.consumer.row = b ∧ link.consumer.slot = slot then copyTupleValue lam (copyEndpointTuple A link.tag link.consumer) else 0)).sum := by
  refine copy_fold_project xs
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) (fun row => row.consumerValues slot)
    (fun link => if link.consumer.row = b ∧ link.consumer.slot = slot then
      copyTupleValue lam (copyEndpointTuple A link.tag link.consumer) else 0) ?_ initial
  intro row link
  change (copyAccumulateEndpoint row.consumerValues row.consumerWeights link.consumer link.tag
    (copyLinkWeight link pub.nextPairIndex pub.variant)
    (copyPatternValuesLiteral (rowOpenings A b).z lam) (copySelectors (rowSel b))).1 slot = _
  rw [copy_accumulate_values, copy_selector_row, copy_selected_endpoint_value]
  by_cases hr : link.consumer.row = b <;> by_cases hs : link.consumer.slot = slot <;>
    simp [hr, hs]

private theorem copy_fold_consumer_weights (xs : List CopyLink) (pub : Public K) (lam : K)
    (A : Trace K) (b : Fin 1024) (initial : CopyRowExtension K) (slot : Fin 2) :
    (xs.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) initial).consumerWeights slot =
      initial.consumerWeights slot + (xs.map (fun link =>
        if link.consumer.row = b ∧ link.consumer.slot = slot then copyLinkWeight link pub.nextPairIndex pub.variant else 0)).sum := by
  refine copy_fold_project xs
    (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) (fun row => row.consumerWeights slot)
    (fun link => if link.consumer.row = b ∧ link.consumer.slot = slot then
      copyLinkWeight link pub.nextPairIndex pub.variant else 0) ?_ initial
  intro row link
  change (copyAccumulateEndpoint row.consumerValues row.consumerWeights link.consumer link.tag
    (copyLinkWeight link pub.nextPairIndex pub.variant)
    (copyPatternValuesLiteral (rowOpenings A b).z lam) (copySelectors (rowSel b))).2 slot = _
  rw [copy_accumulate_weights, copy_selector_row]
  by_cases hr : link.consumer.row = b <;> by_cases hs : link.consumer.slot = slot <;>
    simp [hr, hs, rowSel]

omit [Field K] in
private theorem copy_rows_ext (x y : CopyRowExtension K)
    (hpv : ∀ i, x.producerValues i = y.producerValues i)
    (hpw : ∀ i, x.producerWeights i = y.producerWeights i)
    (hcv : ∀ i, x.consumerValues i = y.consumerValues i)
    (hcw : ∀ i, x.consumerWeights i = y.consumerWeights i) : x = y := by
  cases x; cases y
  cases funext hpv; cases funext hpw; cases funext hcv; cases funext hcw
  rfl

private theorem copy_row_fold (pub : Public K) (lam : K) (A : Trace K) (b : Fin 1024) :
    copyLinks.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ =
      copyRowsAt pub lam A b := by
  apply copy_rows_ext
  · intro i; simpa only [zero_add] using copy_fold_producer_values copyLinks pub lam A b
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ i
  · intro i; simpa only [zero_add] using copy_fold_producer_weights copyLinks pub lam A b
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ i
  · intro i; simpa only [zero_add] using copy_fold_consumer_values copyLinks pub lam A b
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ i
  · intro i; simpa only [zero_add] using copy_fold_consumer_weights copyLinks pub lam A b
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ i

private theorem copy_evaluate_row (pub : Public K) (lam chi : K) (A : Trace K) (b : Fin 1024) :
    (copyEvaluateWithSelectors (rowOpenings A b).z (A 26 b) (copySelectors (rowSel b))
      lam chi pub.nextPairIndex pub.variant).1 =
      if CopyActiveRow b then copyResidual (copyRowsAt pub lam A b) (A 26 b) chi else 0 := by
  change copyActiveLiteral (copySelectors (rowSel b)) * copyResidual
    (copyLinks.foldl (copyAccumulateRow pub (copyPatternValuesLiteral (rowOpenings A b).z lam)
      (copySelectors (rowSel b))) ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩)
    (A 26 b) chi = _
  rw [copy_row_fold, copy_active_row]
  split_ifs <;> simp only [one_mul, zero_mul]

private theorem copy_residual_eq_zero_iff (row : CopyRowExtension K) (helper chi : K) :
    copyResidual row helper chi = 0 ↔
      ((chi - row.producerValues 0) * (chi - row.producerValues 1)) *
        (helper * ((chi - row.consumerValues 0) * (chi - row.consumerValues 1)) +
          (row.consumerWeights 0 * (chi - row.consumerValues 1) +
            row.consumerWeights 1 * (chi - row.consumerValues 0))) =
      ((chi - row.consumerValues 0) * (chi - row.consumerValues 1)) *
        (row.producerWeights 0 * (chi - row.producerValues 1) +
          row.producerWeights 1 * (chi - row.producerValues 0)) := by
  exact sub_eq_zero

/-- T:910–972,1048,1068–1072 on every Boolean row: the complete active-row
LogUp equation, with each slot's ordered tagged tuple compression and weight.
Inactive rows contribute zero; H1 is this trace's A26, without a pointwise
inactive-H1 constraint. No denominator inversion or tuple equality is used. -/
theorem copy_holds_iff (pub : Public K) (lam chi : K) (A : Trace K) :
    CHolds copyFamily pub lam chi A ↔ ∀ b : Fin 1024, CopyActiveRow b →
      let p := copyRowValues A lam b CopyLink.producer
      let pw := copyRowWeights pub b CopyLink.producer
      let c := copyRowValues A lam b CopyLink.consumer
      let cw := copyRowWeights pub b CopyLink.consumer
      ((chi - p 0) * (chi - p 1)) *
        (A 26 b * ((chi - c 0) * (chi - c 1)) +
          (cw 0 * (chi - c 1) + cw 1 * (chi - c 0))) =
      ((chi - c 0) * (chi - c 1)) *
        (pw 0 * (chi - p 1) + pw 1 * (chi - p 0)) := by
  change (∀ b : Fin 1024, ∀ r ∈
    [(copyEvaluateWithSelectors (rowOpenings A b).z (A 26 b) (copySelectors (rowSel b))
      lam chi pub.nextPairIndex pub.variant).1], r = 0) ↔ _
  simp only [List.mem_singleton, forall_eq, copy_evaluate_row]
  constructor
  · intro h b hb
    exact (copy_residual_eq_zero_iff _ _ _).mp (by simpa only [if_pos hb] using h b)
  · intro h b
    by_cases hb : CopyActiveRow b
    · rw [if_pos hb]
      exact (copy_residual_eq_zero_iff _ _ _).mpr (h b hb)
    · rw [if_neg hb]

/-- T:1072: the sole Copy residual is the prescribed zero at inactive rows,
regardless of the current helper cell and the two challenges. -/
theorem copy_inactive_residuals (pub : Public K) (lam chi : K) (A : Trace K)
    (b : Fin 1024) (hb : ¬ CopyActiveRow b) :
    copyFamily.residuals pub lam chi (rowOpenings A b) (A 26 b) (rowSel b) = [0] := by
  change [(copyEvaluateWithSelectors (rowOpenings A b).z (A 26 b) (copySelectors (rowSel b))
    lam chi pub.nextPairIndex pub.variant).1] = [0]
  rw [copy_evaluate_row, if_neg hb]

/-- Pair-forest semantic terminal:1307. This identifies the first helper sum;
it does not assert that the sum vanishes. -/
theorem copy_mu_helper_sum (A : Trace K) (mu : K) :
    (∑ b : Fin 1024, mu * A 26 b) = mu * (∑ b : Fin 1024, A 26 b) := by
  rw [Finset.mul_sum]

/-- Pair-forest semantic terminal:1308. On Boolean rows the second helper sum
is precisely the sum over the literal inactive set. This is an identity,
not an assertion that either helper sum vanishes. -/
theorem copy_mu_inactive_helper_sum (A : Trace K) (mu : K) :
    (∑ b : Fin 1024,
      mu * mu * ((1 - copyActiveLiteral (copySelectors (rowSel b))) * A 26 b)) =
      mu * mu * (∑ b ∈ copyInactiveRows, A 26 b) := by
  rw [← Finset.mul_sum]
  apply congrArg (fun value : K => mu * mu * value)
  rw [copyInactiveRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  rw [copy_active_row]
  by_cases hb : CopyActiveRow b
  · rw [if_pos hb, if_neg (not_not.mpr hb), sub_self, zero_mul]
  · rw [if_neg hb, if_pos hb, sub_zero, one_mul]

#print axioms copy_rows_ext
#print axioms copy_row_fold
#print axioms copy_evaluate_row
#print axioms copy_residual_eq_zero_iff
#print axioms copy_holds_iff
#print axioms copy_inactive_residuals
#print axioms copy_mu_helper_sum
#print axioms copy_mu_inactive_helper_sum

#print axioms copy_fold_producer_values

#print axioms copy_fold_producer_weights

#print axioms copy_fold_consumer_values

#print axioms copy_fold_consumer_weights

#print axioms copy_power_fold
#print axioms copy_powers_eq
#print axioms copy_pattern_fold
#print axioms copy_pattern_values_eq
#print axioms copy_endpoint_value
#print axioms copy_selected_endpoint_value
#print axioms copy_accumulate_values
#print axioms copy_accumulate_weights
#print axioms copy_fold_project

#print axioms copy_selector_row
#print axioms copy_fold_add
#print axioms copy_signed_fold
#print axioms copy_indicator_sum
#print axioms copy_mask_indicator
#print axioms copy_active_sum
#print axioms copy_active_row

#print axioms copy_linkWeight_zero
#print axioms copy_positivity_mem
#print axioms copy_singleton_patterns
#print axioms copy_positivity_links
end R0P
