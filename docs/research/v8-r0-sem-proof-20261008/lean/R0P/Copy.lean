import R0P.CopyConstants

/-! G4 literal explicit-input Copy terminal helpers, source T =
crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs, C = its
_constants.rs, pinned e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.

FINDING: Core.Family cannot express evaluate_with_selectors: H1 is not in
Core.Openings and lambda/chi are not in Core.Public. No copyFamily or
copy_holds_iff is asserted. The explicit-input function below preserves those
inputs. In particular its helper is NOT silently fixed or captured from a
different trace. No LogUp-to-tuple-equality implication is asserted. -/
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

#print axioms copy_linkWeight_zero
#print axioms copy_positivity_mem
#print axioms copy_singleton_patterns
#print axioms copy_positivity_links
end R0P
