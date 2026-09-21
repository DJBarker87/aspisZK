import AspisV8R17.ChordDual

/-! Source chord transpose including padding and even/odd interleaving.
The pairing concerns the retained 1024 coefficients, without asserting the
discarded four high coefficients vanish for an arbitrary quotient. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def interleave (e o : ℕ → F) (i : ℕ) : F :=
  if i%2=0 then e (i/2) else o (i/2)

theorem sum_range_parity (n : ℕ) (f : ℕ → F) :
    (∑ i ∈ Finset.range (2*n), f i) =
      ∑ i ∈ Finset.range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)= (2*n+1)+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem interleave_even (e o : ℕ → F) (i : ℕ) : interleave e o (2*i) = e i := by
  simp [interleave]

theorem interleave_odd (e o : ℕ → F) (i : ℕ) : interleave e o (2*i+1) = o i := by
  simp [interleave, Nat.add_div]

theorem rangeDot_interleave (n : ℕ) (w e o : ℕ → F) :
    rangeDot (2*n) w (interleave e o) =
      rangeDot n (fun i => w (2*i)) e + rangeDot n (fun i => w (2*i+1)) o := by
  unfold rangeDot
  rw [sum_range_parity]
  simp only [interleave_even, interleave_odd, Finset.sum_add_distrib]

def sourceChordTranspose (half : F) (w : ℕ → F) (a b c : F) : ℕ → F :=
  let we := zeroExtend 512 (fun i => w (2*i))
  let wo := zeroExtend 512 (fun i => w (2*i+1))
  interleave (chordDualEven half we wo a b c) (chordDualOdd half we wo a b c)

theorem source_chord_transpose_pairing (half : F) (q w : ℕ → F) (a b c : F) :
    rangeDot 1024 w (sourceChord half q a b c) =
      rangeDot 1024 (sourceChordTranspose half w a b c) q := by
  have h := source_chord_lane_pairing half q
    (zeroExtend 512 (fun i => w (2*i))) (zeroExtend 512 (fun i => w (2*i+1))) a b c
  rw [rangeDot_comm 514 (zeroExtend 512 (fun i => w (2*i))),
    rangeDot_comm 514 (zeroExtend 512 (fun i => w (2*i+1))),
    rangeDot_zeroExtend 512 514 (by omega), rangeDot_zeroExtend 512 514 (by omega)] at h
  rw [rangeDot_comm 512 _ (fun i => w (2*i)),
    rangeDot_comm 512 _ (fun i => w (2*i+1))] at h
  change rangeDot (2*512) w (interleave
    (finiteChordEven 512 (sourceEdges half 512) (sourceEdges half 513) q a b c)
    (finiteChordOdd 512 (sourceEdges half 512) q a b c)) = _
  rw [rangeDot_interleave, rangeDot_comm 1024 (sourceChordTranspose half w a b c)]
  unfold sourceChordTranspose
  rw [rangeDot_interleave 512,
    rangeDot_comm 512 (fun i => q (2*i)), rangeDot_comm 512 (fun i => q (2*i+1))]
  exact h

#print axioms sum_range_parity
#print axioms rangeDot_interleave
#print axioms source_chord_transpose_pairing
end AspisV8R17
