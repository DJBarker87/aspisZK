import NJC_ScanViews
set_option autoImplicit false
noncomputable section
namespace NJJ_Chunks
open Aeneas Aeneas.Std Result
/-- Rule-3 value model for ChunksExact. `remaining` retains all bytes, including
an incomplete final suffix. `next` leaves that suffix in the iterator. -/
structure State (T : Type) where
 remaining : List T
 width : Nat

def next {T : Type} (s : State T) : Option (List T) × State T :=
 if 0<s.width ∧ s.width≤s.remaining.length then
  (some (s.remaining.take s.width),⟨s.remaining.drop s.width,s.width⟩)
 else (none,s)

def remainder {T : Type} (s : State T) :=
 s.remaining.drop (s.remaining.length/s.width*s.width)

/-- Complete chunk and all remaining bytes, rather than only a length law. -/
theorem step {T : Type} (s : State T) (live : 0<s.width)
 (fit : s.width≤s.remaining.length) :
 next s=(some (s.remaining.take s.width),⟨s.remaining.drop s.width,s.width⟩) := by
 simp only [next,live,fit,and_self,if_true]

theorem end_frame {T : Type} (s : State T) (ended : s.remaining.length<s.width) :
 next s=(none,s) := by
 simp only [next,show ¬(0<s.width ∧ s.width≤s.remaining.length) from by omega,if_false]

/-- Any number of complete native steps preserves the untouched byte suffix.
No whole-buffer normalization; the proof is the drop/drop frame induction. -/
theorem window {T : Type} (xs : List T) (off n width : Nat) :
 ((xs.drop off).drop (n*width)).take width=(xs.drop (off+n*width)).take width := by
 rw [List.drop_drop]

/-- Logical history/frame composition, including trailing incomplete bytes. -/
theorem frame {T : Type} (xs : List T) (width n : Nat) :
 (xs.drop (n*width)).drop width=xs.drop ((n+1)*width) := by
 rw [List.drop_drop]
 congr 1
 omega

/-- The SAME scan window:32-byte field cells in the final64 region. -/
theorem final (proof : List U8) (i : Nat) (inside : i<64) :
 (((proof.drop 7783).take 2272).drop (32*(7+i))).take 32=
 (proof.drop (8007+32*i)).take 32 := NJC_ScanViews.final proof i inside

#print axioms step
#print axioms end_frame
#print axioms window
#print axioms frame
#print axioms final
end NJJ_Chunks
