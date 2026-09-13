import FSBoundedTranscript

/-!
Source-specific deterministic decoder leaves for the ordinary QM31 challenge.

These statements use the pinned `FSBoundedTranscript` source model.  They do
not assert that an actual oracle answer is fresh or uniform, and they do not
use the first-block fallback in a probability argument.
-/
set_option autoImplicit false
namespace AspisV8Completion.FSV8SourceBufferedDecode
open FSOracleExecution
open FSBoundedTranscript

/-- A buffered run of sentinels followed by a canonical value is consumed
without another squeeze, provided it is shorter than the limb retry cap. -/
theorem limb_buffer_of_sentinel_prefix
    (tape : Tape) (t : Transcript) (k cap x : Nat) (tail : List Nat)
    (room : k < cap) (canonical : x ≠ 2147483647) :
    limb tape cap ⟨t, List.replicate k 2147483647 ++ x :: tail⟩ =
      (some x, ⟨t, tail⟩) := by
  induction k generalizing cap with
  | zero =>
      cases cap with
      | zero => omega
      | succ cap => simp [limb, nextWord, canonical]
  | succ k ih =>
      cases cap with
      | zero => omega
      | succ cap =>
          have smaller : k < cap := Nat.lt_of_succ_lt_succ room
          simpa only [List.replicate_succ, List.cons_append, limb, nextWord,
            if_pos rfl, if_true] using ih cap smaller

/-- All four accepted values can be supplied from one buffered word stream,
with any legal in-buffer rejection pattern. -/
theorem four_limbs_from_one_buffer
    (tape : Tape) (t : Transcript)
    (r0 r1 r2 r3 a0 a1 a2 a3 : Nat) (tail : List Nat)
    (h0 : r0 < 8) (h1 : r1 < 8) (h2 : r2 < 8) (h3 : r3 < 8)
    (a0ok : a0 ≠ 2147483647) (a1ok : a1 ≠ 2147483647)
    (a2ok : a2 ≠ 2147483647) (a3ok : a3 ≠ 2147483647) :
    limbs tape 4 ⟨t,
      List.replicate r0 2147483647 ++ a0 ::
      (List.replicate r1 2147483647 ++ a1 ::
      (List.replicate r2 2147483647 ++ a2 ::
      (List.replicate r3 2147483647 ++ a3 :: tail)))⟩ =
        (some [a0, a1, a2, a3], ⟨t, tail⟩) := by
  simp [limbs, limb_buffer_of_sentinel_prefix, h0, h1, h2, h3,
    a0ok, a1ok, a2ok, a3ok]

/-- Deterministic first-block pattern endpoint.  The block-pattern premise is
a literal decoder fact, not a freshness or uniformity premise. -/
theorem challenge_first_block_pattern
    (tape : Tape) (before after : Transcript) (block : Block)
    (squeezed : squeeze tape before = (block, after))
    (r0 r1 r2 r3 a0 a1 a2 a3 : Nat) (tail : List Nat)
    (pattern : words block =
      List.replicate r0 2147483647 ++ a0 ::
      (List.replicate r1 2147483647 ++ a1 ::
      (List.replicate r2 2147483647 ++ a2 ::
      (List.replicate r3 2147483647 ++ a3 :: tail))))
    (h0 : r0 < 8) (h1 : r1 < 8) (h2 : r2 < 8) (h3 : r3 < 8)
    (a0ok : a0 ≠ 2147483647) (a1ok : a1 ≠ 2147483647)
    (a2ok : a2 ≠ 2147483647) (a3ok : a3 ≠ 2147483647) :
    challenge tape before = (some [a0, a1, a2, a3], after) := by
  simp only [challenge, squeezed, pattern]
  rw [four_limbs_from_one_buffer tape after r0 r1 r2 r3 a0 a1 a2 a3
    tail h0 h1 h2 h3 a0ok a1ok a2ok a3ok]

/-- An all-sentinel first block exhausts the first limb and rejects. -/
theorem challenge_first_block_all_sentinel
    (tape : Tape) (before after : Transcript) (block : Block)
    (squeezed : squeeze tape before = (block, after))
    (pattern : words block = List.replicate 8 2147483647) :
    challenge tape before = (none, after) := by
  simp [challenge, squeezed, pattern, limbs, limb, nextWord]

#print axioms limb_buffer_of_sentinel_prefix
#print axioms four_limbs_from_one_buffer
#print axioms challenge_first_block_pattern
#print axioms challenge_first_block_all_sentinel
end AspisV8Completion.FSV8SourceBufferedDecode
