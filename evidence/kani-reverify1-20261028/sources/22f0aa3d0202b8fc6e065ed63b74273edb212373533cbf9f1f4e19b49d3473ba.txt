import KMY_SerializerComposition
set_option autoImplicit false
namespace KMY_CheckpointComposition
open KMX_CopyMeaning KMY_WindowComposition KMY_SerializerComposition

theorem append32 (value before : Nat → Nat) (len j : Nat) (h : j < len+32) :
    window value before len 32 j = if j<len then before j else value (j-len) :=
  append_window value before len 32 j h

theorem query_word_append (byte before : Nat → Nat) (len j : Nat) (h : j < len+4) :
    window byte before len 4 j = if j<len then before j else byte (j-len) :=
  append_window byte before len 4 j h

theorem put_k_arbitrary_prefix (limbByte : Nat → Nat → Nat) (before : Nat → Nat)
    (len j : Nat) (h : j < len+16) :
    window (fun b => limbByte (b/4) (b%4)) before len 16 j =
      if j<len then before j else limbByte ((j-len)/4) ((j-len)%4) :=
  append_window _ before len 16 j h

theorem put_e_arbitrary_prefix (limbByte : Nat → Nat → Nat) (before : Nat → Nat)
    (len j : Nat) (h : j < len+32) :
    window (fun b => limbByte (b/4) (b%4)) before len 32 j =
      if j<len then before j else limbByte ((j-len)/4) ((j-len)%4) :=
  append_window _ before len 32 j h

theorem selected_reference_write (limbByte : Nat → Nat → Nat) (before : Nat → Nat)
    (i j : Nat) (h : j < 712+16*i+16) :
    window (fun b => limbByte (b/4) (b%4)) before (712+16*i) 16 j =
      if j<712+16*i then before j
      else limbByte ((j-(712+16*i))/4) ((j-(712+16*i))%4) :=
  put_k_arbitrary_prefix limbByte before _ j h

theorem checksum_projection (initial answer : Nat → Nat) (j : Nat) (h : j<1768) :
    window answer initial 1736 32 j =
      if j<1736 then initial j else answer (j-1736) :=
  append_window answer initial 1736 32 j (by omega)

def digestPrefix (before hp hu state : Nat → Nat) : Nat → Nat :=
  window state (window hu (window hp before 16 32) 48 32) 80 32

theorem digest_prefix_cut (before hp hu state : Nat → Nat) (j : Nat) (h : j<112) :
    digestPrefix before hp hu state j =
      if j<16 then before j else if j<48 then hp (j-16)
      else if j<80 then hu (j-48) else state (j-80) := by
  simp only [digestPrefix, window_spec]
  by_cases h0 : j<16
  · have a : ¬ (80 ≤ j ∧ j < 80+32) := by omega
    have b : ¬ (48 ≤ j ∧ j < 48+32) := by omega
    have c : ¬ (16 ≤ j ∧ j < 16+32) := by omega
    simp only [if_pos h0, if_neg a, if_neg b, if_neg c]
  · by_cases h1 : j<48
    · have a : ¬ (80 ≤ j ∧ j < 80+32) := by omega
      have b : ¬ (48 ≤ j ∧ j < 48+32) := by omega
      have c : 16 ≤ j ∧ j < 16+32 := by omega
      simp only [if_neg h0, if_pos h1, if_neg a, if_neg b, if_pos c]
    · by_cases h2 : j<80
      · have a : ¬ (80 ≤ j ∧ j < 80+32) := by omega
        have b : 48 ≤ j ∧ j < 48+32 := by omega
        simp only [if_neg h0, if_neg h1, if_pos h2, if_neg a, if_pos b]
      · have a : 80 ≤ j ∧ j < 80+32 := by omega
        simp only [if_neg h0, if_neg h1, if_neg h2, if_pos a]

def rootsQueries (roots query before : Nat → Nat) : Nat → Nat :=
  window query (window roots before 0 64) 64 88

theorem roots_queries_cut (roots query before : Nat → Nat) (j : Nat) (h : j<152) :
    rootsQueries roots query before j = if j<64 then roots j else query (j-64) := by
  simp only [rootsQueries, window_spec]
  by_cases h0 : j<64
  · have a : ¬ (64 ≤ j ∧ j < 64+88) := by omega
    have b : 0 ≤ j ∧ j < 0+64 := by omega
    simp only [if_pos h0, if_neg a, if_pos b, Nat.sub_zero]
  · have a : 64 ≤ j ∧ j < 64+88 := by omega
    simp only [if_neg h0, if_pos a]

/-- The fourteen scalar windows in semantic-alpha and the two z points. -/
theorem semantic_z_cut (semantic : Nat → Nat → Nat) (z : Nat → Nat → Nat → Nat)
    (before : Nat → Nat) (j : Nat) (h : j<224) :
    windows (fun b => if b<160 then semantic (b/16) (b%16)
      else z ((b-160)/32) (((b-160)%32)/16) (b%16)) before 0 16 14 j =
      if j<160 then semantic (j/16) (j%16)
      else z ((j-160)/32) (((j-160)%32)/16) (j%16) := by
  rw [windows_spec, if_pos (by omega)]

theorem weights_copy_value {α : Type} (raw before : Nat → α) (j : Nat) (h : j<64) :
    loop raw before 0 64 j = raw j := by
  rw [copy_prefix, if_pos h]

#print axioms append32
#print axioms query_word_append
#print axioms put_k_arbitrary_prefix
#print axioms put_e_arbitrary_prefix
#print axioms selected_reference_write
#print axioms checksum_projection
#print axioms digest_prefix_cut
#print axioms roots_queries_cut
#print axioms semantic_z_cut
#print axioms weights_copy_value
end KMY_CheckpointComposition
