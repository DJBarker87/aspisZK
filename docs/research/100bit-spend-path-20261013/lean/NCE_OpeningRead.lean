import NBY_OpeningLocality
import NCE_FirstFailure

set_option autoImplicit false
namespace AspisR1.NCE_OpeningCuts
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- One shared caller carrier. The native read cut must preserve these
actual fields, rather than selecting independent successful child witnesses. -/
structure Carrier where
  prepared : VTop_Stages.verifier.Prepared
  proof : Slice U8
  scratch : reference.Scratch
  log : NCE_FirstFailure.Log

abbrev Reader := Carrier → Nat → Result (U8 × Carrier)

/-- ONE selected proof byte/reborrow on arbitrary SAME caller state; no
whole-opening, accepted child, successful padding or final-log premise.
A native harness must identify this reader with its actual backing pointer. -/
def NCE_Native_Opening (reader : Reader) : Prop :=
  ∀ (s : Carrier) (i w c : Nat), s.proof.val.length = 57607 →
    i < 22 → w < 26 → c < 32 →
    reader s (10055+832*i+32*w+c) =
      ok (s.proof.val[10055+832*i+32*w+c]!,s)

/-- Existing Euclidean window coverage derives the selected reader law at
any opening coordinate. It does not introduce a second proof allocation. -/
theorem read_byte (reader : Reader) (cut : NCE_Native_Opening reader)
    (s : Carrier) (i k : Nat) (size : s.proof.val.length = 57607)
    (ib : i < 22) (kb : k < 832) :
    reader s (10055+832*i+k) = ok (s.proof.val[10055+832*i+k]!,s) := by
  have address : 10055+832*i+32*(k/32)+k%32 = 10055+832*i+k := by omega
  have read := cut s i (k/32) (k%32) size ib (by omega) (Nat.mod_lt k (by decide))
  simpa only [address] using read

#print axioms read_byte
end AspisR1.NCE_OpeningCuts
