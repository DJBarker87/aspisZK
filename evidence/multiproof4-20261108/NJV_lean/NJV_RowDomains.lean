import NJV_NativeRows
import NJP_RowInvariant

set_option autoImplicit false
noncomputable section
namespace NJV_RowDomains
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Every native cut invocation receives the domain its Kani proof assumed;
no additional per-iteration preconditions are placed on the final root. -/
theorem next_domain (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
    (domain : Domain length s i w) (active : i<s.n)
    (cut : NJP_NativeRowCut.Cut s i w length nodes
      (H (NJP_NativeRowCut.request log)) after ni nw true log) :
 after.n=s.n ∧ Domain length after ni nw ∧ i<ni ∧ nw=w+1 := by
 obtain ⟨out,returned,progress⟩ := NJP_RowInvariant.node_progress H nodes length s i w domain active
 have observed := NJP_NativeStep.one H nodes length s i w after ni nw true log cut
 have same := congrArg Prod.snd observed
 simp only [returned,ite_true] at same
 have rowEq := Result.ok.inj same
 rw [rowEq] at progress
 exact progress

inductive Admissible (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → Nat → Nat → List (Request × Digest) → Level → Prop where
 | halt (fuel : Nat) (s : Scratch) (i w : Nat) (halted : s.n ≤ i)
     (domain : Domain length s i w) :
   Admissible H nodes length fuel s i w [] (.done {s with n:=w})
 | stop (fuel : Nat) (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
     (active : i<s.n) (domain : Domain length s i w)
     (cut : NJP_NativeRowCut.Cut s i w length nodes
       (H (NJP_NativeRowCut.request log)) after ni nw false log) :
   Admissible H nodes length (fuel+1) s i w (NJV_NativeRows.events H log) (.stop after)
 | next (fuel : Nat) (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
     (history : List (Request × Digest)) (out : Level) (active : i<s.n)
     (domain : Domain length s i w)
     (cut : NJP_NativeRowCut.Cut s i w length nodes
       (H (NJP_NativeRowCut.request log)) after ni nw true log)
     (tail : Admissible H nodes length fuel after ni nw history out) :
   Admissible H nodes length (fuel+1) s i w (NJV_NativeRows.events H log++history) out

theorem all (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s : Scratch) (i w : Nat) (history : List (Request × Digest)) (out : Level)
    (native : NJV_NativeRows.Invocation H nodes length fuel s i w history out)
    (domain : Domain length s i w) :
 Admissible H nodes length fuel s i w history out := by
 induction native with
 | halt fuel s i w halted => exact .halt fuel s i w halted domain
 | stop fuel s after i w ni nw log active cut =>
   exact .stop fuel s after i w ni nw log active domain cut
 | next fuel s after i w ni nw log history out active cut tail ih =>
   have progress := next_domain H nodes length s after i w ni nw log domain active cut
   exact .next fuel s after i w ni nw log history out active domain cut (ih progress.2.1)

#print next_domain
#print axioms next_domain
#print all
#print axioms all
end NJV_RowDomains
end
