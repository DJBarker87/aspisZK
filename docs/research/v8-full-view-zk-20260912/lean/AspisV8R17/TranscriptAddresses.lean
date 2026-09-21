import AspisV8PairedCommitment.Domains

/-! Literal byte grammars from transcript.rs and the retained V7 private
commitments. Grammar overlap is not a reachable SHA-state attack. -/
set_option autoImplicit false
namespace AspisV8R17.TranscriptAddresses
open AspisV8PairedCommitment

def squeezeInput (state : List Byte) : List Byte := state ++ [1]
def advanceInput (state : List Byte) : List Byte := state ++ [2]
def absorbInput (state : List Byte) (label : Byte) (data : List Byte) : List Byte :=
  state ++ [0,label] ++ data

theorem squeeze_length (state : List Byte) (hs : state.length = 32) :
    (squeezeInput state).length = 33 := by simp [squeezeInput, hs]

theorem advance_length (state : List Byte) (hs : state.length = 32) :
    (advanceInput state).length = 33 := by simp [advanceInput, hs]

theorem squeeze_ne_advance (s t : List Byte) : squeezeInput s ≠ advanceInput t := by
  intro h
  have hh := congrArg List.reverse h
  simp only [squeezeInput, advanceInput, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append] at hh
  have bad : (1 : Byte) = 2 := (List.cons.inj hh).1
  exact (by decide : (1 : Byte) ≠ 2) bad

theorem short_ne_leaf (input value salt : List Byte) (tag : Byte)
    (hi : input.length = 33) (hs : salt.length = 32) :
    input ≠ leafInput tag value salt := by
  intro h
  have hl := leaf_input_length tag value salt hs
  rw [← h, hi] at hl
  omega

theorem short_ne_parent (input left right : List Byte)
    (hi : input.length = 33) (hl : left.length = 26) (hr : right.length = 26) :
    input ≠ parentInput left right := by
  intro h
  have hp := parent_input_length left right hl hr
  rw [← h, hi] at hp
  omega

theorem absorb_two_flatten (state first second : List Byte) (label : Byte) :
    absorbInput state label (first ++ second) =
      (state ++ [0,label] ++ first) ++ second := by
  simp [absorbInput, List.append_assoc]

/-- Both byte grammars admit this same address with a 32-byte state and
32-byte salt. This does NOT establish reachability of that state or record. -/
theorem absorb_leaf_grammar_overlap (tag label : Byte) (payload salt : List Byte)
    (hs : salt.length = 32) :
    ∃ state value data : List Byte,
      state.length = 32 ∧ salt.length = 32 ∧ value.length = 32 + payload.length ∧
      absorbInput state label data = leafInput tag value salt := by
  refine ⟨16::tag::List.replicate 30 0,
    List.replicate 30 0 ++ [0,label] ++ payload, payload ++ salt, ?_, hs, ?_, ?_⟩
  · simp
  · simp; omega
  · simp [absorbInput, leafInput, List.append_assoc]

#print axioms squeeze_length
#print axioms advance_length
#print axioms squeeze_ne_advance
#print axioms short_ne_leaf
#print axioms short_ne_parent
#print axioms absorb_two_flatten
#print axioms absorb_leaf_grammar_overlap
end AspisV8R17.TranscriptAddresses
