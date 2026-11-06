import LPt_LPl_EcheckResult
import NJJ_Chunks
set_option autoImplicit false
noncomputable section
namespace NJZ_Echeck
open Aeneas Aeneas.Std Result
abbrev Words := Fin 8 → Nat
attribute [local instance] Classical.propDecidable

def Canonical (w : Words) := ∀ i,w i<2147483647
def HighZero (w : Words) := ∀ i : Fin 8,4≤i.val→w i=0
def decode (w : Words) : Option Words := if Canonical w then some w else none
def step (reply : Option Words) (k : Bool) : Bool :=
 match reply with
 | none => false
 | some w => !k || decide (HighZero w)

/-- Exact scalar verdict transcribed from K006/K007 after parser substitution.
The full native Option/limbs and byte-window observations are retained in the
certificate; this is its Bool projection, not a native parser theorem. -/
def StepCut (reply : Option Words) (k out : Bool) := out=step reply k

theorem step_iff (w : Words) (k : Bool) :
 step (decode w) k=true ↔ Canonical w ∧ (k=true→HighZero w) := by
 unfold step decode
 by_cases canonical : Canonical w
 · rw [if_pos canonical]
   cases k <;> simp [canonical]
 · rw [if_neg canonical]
   simp [canonical]

def words (bs : List U8) : Words := fun i=>
 LPt_LPl.Echeck.word ((bs.drop (4*i.val)).take 4)

/-- Exact natural-byte guard, with every rejected and high-nonzero word. -/
theorem chunk_iff (bs : List U8) (k : Bool) :
 LPt_LPl.Echeck.chunk bs k=true ↔
 Canonical (words bs) ∧ (k=true→HighZero (words bs)) := by
 unfold LPt_LPl.Echeck.chunk
 rw [List.all_eq_true]
 constructor
 · intro all
   constructor
   · intro i
     have h:=all i.val (List.mem_range.mpr i.isLt)
     have pair : decide (words bs i<2147483647)=true ∧ _ := by simpa [words] using h
     exact of_decide_eq_true pair.1
   · intro hk i large
     have pair : decide (words bs i<2147483647)=true ∧
       (!k || decide (i.val<4 ∨ words bs i=0))=true := by
      simpa [words] using all i.val (List.mem_range.mpr i.isLt)
     have h:=pair.2
     rw [hk] at h
     have hz : i.val<4 ∨ words bs i=0 := by simpa [words] using h
     rcases hz with small|zero
     · omega
     · exact zero
 · rintro ⟨canonical,high⟩ i inside
   have hi : i<8 := List.mem_range.mp inside
   suffices both : decide (words bs ⟨i,hi⟩<2147483647)=true ∧
     (!k || decide (i<4 ∨ words bs ⟨i,hi⟩=0))=true by simpa [words] using both
   refine ⟨by exact decide_eq_true (canonical ⟨i,hi⟩),?_⟩
   cases hk:k with
   | false => rfl
   | true =>
     have h : i<4 ∨ words bs ⟨i,hi⟩=0 := by
      by_cases small:i<4
      · exact Or.inl small
      · exact Or.inr (high hk ⟨i,hi⟩ (by omega))
     simpa [words] using (decide_eq_true h)

theorem step_chunk (bs : List U8) (k : Bool) :
 step (decode (words bs)) k=LPt_LPl.Echeck.chunk bs k := by
 apply Bool.eq_iff_iff.mpr
 exact (step_iff _ _).trans (chunk_iff _ _).symm

/-- Native one-step verdict at an arbitrary source position after the complete
codec guard is installed on the SAME selected bytes. -/
theorem at_window (bs : List U8) (k : Bool) (i : Nat) (out : Bool)
 (cut : StepCut (decode (words ((bs.drop (32*i)).take 32))) k out) :
 out=LPt_LPl_A.Echeck.predicate bs k i := by
 rw [cut,step_chunk,LPt_LPl.Echeck.chunk_eq]
 rfl

/-- Retained first-error induction covers all complete chunks, including
ignored incomplete suffixes. This composes local verdicts; it does not assert
that an unreviewed raw extraction equals the source. -/
theorem result (bs : Slice U8) (k out : Bool)
 (trace : LPt_LPl.Echeck.Trace bs.val k 0 out) :
 LPt_LPl_Kit_Release.LPt_External.verifier.echeck bs k=
 ok (if out then .Ok () else .Err .Parse) :=
 LPt_LPl.Echeck.native_result bs k out trace

#print axioms step_iff
#print axioms chunk_iff
#print axioms step_chunk
#print axioms at_window
#print axioms result
end NJZ_Echeck
