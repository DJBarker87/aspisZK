import AspisFormal.Pool.V7MerkleParserRoundtrip

/-!
# Congruence of complete Merkle extraction on typed hash inputs

The Tag-73 verifier can extend the prover's shared SHA table with transcript
queries which are not Merkle preimages.  Complete-tree extraction therefore
must not require equality of the two hash views on arbitrary byte strings.
This file proves that equality on typed Merkle inputs is sufficient whenever
the searched query log itself contains only typed Merkle inputs.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleTypedTruncateCongruence

open AspisPool.V7MerkleParserRoundtrip
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar

theorem defaultC1SubtreeDigest_eq_of_agree_on_typed
    (left right : RawHashInput → Digest208)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    ∀ height, defaultC1SubtreeDigest left height =
      defaultC1SubtreeDigest right height := by
  intro height
  induction height with
  | zero =>
      unfold defaultC1SubtreeDigest c1LeafDigest
      apply agree
      simp [parse_serialize_typed_preimage]
  | succ height inductionHypothesis =>
      simp only [defaultC1SubtreeDigest]
      rw [inductionHypothesis]
      unfold nodeDigest
      apply agree
      simp [parse_serialize_typed_preimage]

theorem defaultC2SubtreeDigest_eq_of_agree_on_typed
    (left right : RawHashInput → Digest208)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    ∀ height, defaultC2SubtreeDigest left height =
      defaultC2SubtreeDigest right height := by
  intro height
  induction height with
  | zero =>
      unfold defaultC2SubtreeDigest c2LeafDigest
      apply agree
      simp [parse_serialize_typed_preimage]
  | succ height inductionHypothesis =>
      simp only [defaultC2SubtreeDigest]
      rw [inductionHypothesis]
      unfold nodeDigest
      apply agree
      simp [parse_serialize_typed_preimage]

theorem resolveFirstAux_eq_of_agree_on_typed_log
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    ∀ target offset,
      resolveFirstAux left target offset log =
        resolveFirstAux right target offset log := by
  induction log with
  | nil => intro target offset; rfl
  | cons head tail inductionHypothesis =>
      intro target offset
      have headTyped : parseTypedPreimage head ≠ none :=
        typedLog head (by simp)
      have tailTyped : ∀ input ∈ tail,
          parseTypedPreimage input ≠ none := by
        intro input member
        exact typedLog input (by simp [member])
      have headAgree := agree head headTyped
      simp only [resolveFirstAux]
      rw [headAgree]
      by_cases hit : right head = target
      · simp [hit]
      · simp [hit, inductionHypothesis tailTyped target (offset + 1)]

theorem resolveFirst_eq_of_agree_on_typed_log
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) (target : Digest208) :
    resolveFirst left target log = resolveFirst right target log := by
  exact resolveFirstAux_eq_of_agree_on_typed_log left right log typedLog agree
    target 0

theorem classifyReference_eq_of_agree_on_typed_log
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) (target : Digest208) (parent : Nat) :
    classifyReference left target parent log =
      classifyReference right target parent log := by
  have takeTyped : ∀ input ∈ log.take parent,
      parseTypedPreimage input ≠ none := by
    intro input member
    exact typedLog input (List.mem_of_mem_take member)
  have dropTyped : ∀ input ∈ log.drop parent,
      parseTypedPreimage input ≠ none := by
    intro input member
    exact typedLog input (List.mem_of_mem_drop member)
  unfold classifyReference
  rw [resolveFirstAux_eq_of_agree_on_typed_log left right (log.take parent)
    takeTyped agree target 0]
  rw [resolveFirstAux_eq_of_agree_on_typed_log left right (log.drop parent)
    dropTyped agree target parent]

theorem extractC1Subtree_eq_of_agree_on_typed
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    ∀ height expectedDigest queryIndex,
      extractC1Subtree left log height expectedDigest queryIndex =
        extractC1Subtree right log height expectedDigest queryIndex := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex
      simp only [extractC1Subtree]
      cases inputExact : log[queryIndex]? with
      | none => simp [inputExact]
      | some input =>
          have inputMem : input ∈ log := List.mem_of_getElem? inputExact
          have inputAgree := agree input (typedLog input inputMem)
          simp [inputExact, inputAgree]
  | succ height inductionHypothesis =>
      intro expectedDigest queryIndex
      simp only [extractC1Subtree]
      cases inputExact : log[queryIndex]? with
      | none => simp [inputExact]
      | some input =>
          have inputMem : input ∈ log := List.mem_of_getElem? inputExact
          have inputAgree := agree input (typedLog input inputMem)
          have defaultAgree :=
            defaultC1SubtreeDigest_eq_of_agree_on_typed left right agree height
          have classifyAgree : ∀ child,
              classifyReference left child queryIndex log =
                classifyReference right child queryIndex log := by
            intro child
            exact classifyReference_eq_of_agree_on_typed_log left right log
              typedLog agree child queryIndex
          simp [inputExact, inputAgree, defaultAgree, classifyAgree,
            inductionHypothesis]

theorem extractC2Subtree_eq_of_agree_on_typed
    (left right : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    ∀ height expectedDigest queryIndex,
      extractC2Subtree left log height expectedDigest queryIndex =
        extractC2Subtree right log height expectedDigest queryIndex := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex
      simp only [extractC2Subtree]
      cases inputExact : log[queryIndex]? with
      | none => simp [inputExact]
      | some input =>
          have inputMem : input ∈ log := List.mem_of_getElem? inputExact
          have inputAgree := agree input (typedLog input inputMem)
          simp [inputExact, inputAgree]
  | succ height inductionHypothesis =>
      intro expectedDigest queryIndex
      simp only [extractC2Subtree]
      cases inputExact : log[queryIndex]? with
      | none => simp [inputExact]
      | some input =>
          have inputMem : input ∈ log := List.mem_of_getElem? inputExact
          have inputAgree := agree input (typedLog input inputMem)
          have defaultAgree :=
            defaultC2SubtreeDigest_eq_of_agree_on_typed left right agree height
          have classifyAgree : ∀ child,
              classifyReference left child queryIndex log =
                classifyReference right child queryIndex log := by
            intro child
            exact classifyReference_eq_of_agree_on_typed_log left right log
              typedLog agree child queryIndex
          simp [inputExact, inputAgree, defaultAgree, classifyAgree,
            inductionHypothesis]

theorem extractCompleteWords_eq_of_agree_on_typed
    (left right : RawHashInput → Digest208) (roots : Roots)
    (log : OrderedRawQueryLog)
    (typedLog : ∀ input ∈ log, parseTypedPreimage input ≠ none)
    (agree : ∀ input, parseTypedPreimage input ≠ none →
      left input = right input) :
    extractCompleteWords left roots log = extractCompleteWords right roots log := by
  unfold extractCompleteWords
  rw [resolveFirst_eq_of_agree_on_typed_log left right log typedLog agree roots.c1]
  rw [resolveFirst_eq_of_agree_on_typed_log left right log typedLog agree roots.c2]
  cases c1Resolved : resolveFirst right roots.c1 log with
  | none => simp [c1Resolved]
  | some c1Index =>
      cases c2Resolved : resolveFirst right roots.c2 log with
      | none => simp [c1Resolved, c2Resolved]
      | some c2Index =>
          simp only [c1Resolved, c2Resolved]
          rw [extractC1Subtree_eq_of_agree_on_typed left right log typedLog
            agree treeDepth roots.c1 c1Index]
          rw [extractC2Subtree_eq_of_agree_on_typed left right log typedLog
            agree treeDepth roots.c2 c2Index]

#print axioms defaultC1SubtreeDigest_eq_of_agree_on_typed
#print axioms defaultC2SubtreeDigest_eq_of_agree_on_typed
#print axioms resolveFirstAux_eq_of_agree_on_typed_log
#print axioms classifyReference_eq_of_agree_on_typed_log
#print axioms extractC1Subtree_eq_of_agree_on_typed
#print axioms extractC2Subtree_eq_of_agree_on_typed
#print axioms extractCompleteWords_eq_of_agree_on_typed

end AspisPool.V7MerkleTypedTruncateCongruence
