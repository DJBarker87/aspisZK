import FinishDotSourceABI
import S4N8WideFromLimbsABI
import AspisR1FastDotsCurrent.FunsOpsV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent

namespace AspisR1FastDotsTailFinishSourceMapV1

abbrev Tail := AspisR1FastDotsCurrent.fast_pairing.EbyKDot
abbrev PushState := AspisR1FinishDotSourceABI.PushState
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE
abbrev FinishWide := AspisR1EbyKFinish.field.wide_exact.WideExact
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps

/-- Literal carrier map: preserve both four-word accumulators and the count. -/
def tailToPushState (s : Tail) : PushState :=
  { c0 := { sums := s.c0.sums }
    c1 := { sums := s.c1.sums }
    count := s.count }

theorem tailToPushState_fields (s : Tail) :
    (tailToPushState s).c0.sums = s.c0.sums ∧
    (tailToPushState s).c1.sums = s.c1.sums ∧
    (tailToPushState s).count = s.count := by
  exact ⟨rfl,rfl,rfl⟩

/-- Coordinate-preserving bridge from the finish proof's FinishE carrier to
    the extracted Finish WideExact carrier consumed by the checked ABI map. -/
def finishEToFinishWide (x : FinishE) : FinishWide :=
  { c0 := { c0 := { a := x.c0.c0.a, b := x.c0.c0.b }
            c1 := { a := x.c0.c1.a, b := x.c0.c1.b } }
    c1 := { c0 := { a := x.c1.c0.a, b := x.c1.c0.b }
            c1 := { a := x.c1.c1.a, b := x.c1.c1.b } } }

def finishEToCurrent (x : FinishE) : CurrentWide :=
  AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent (finishEToFinishWide x)

def currentFinishWords (x : CurrentWide) : List Std.U32 :=
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
   x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

def finishTailCurrent (s : Tail) : Result CurrentWide := do
  let out ← AspisR1FinishDotSourceABI.finishFromPush (tailToPushState s)
  ok (finishEToCurrent out)

/-- This adapter installs the checked EbyKFinish ABI implementation in the
    generated S4 finish slot. Its relationship to the frozen Rust call remains
    a separate source/ABI boundary. -/
def withSourceTailFinish (ops : Ops) : Ops :=
  { ops with ebyKFinish := finishTailCurrent }

theorem withSourceTailFinish_binding (ops : Ops) (s : Tail) :
    (withSourceTailFinish ops).ebyKFinish s = finishTailCurrent s := rfl

theorem finishEToCurrent_words (x : FinishE) :
    currentFinishWords (finishEToCurrent x) =
      AspisR1FinishDotSourceABI.finishWords x := rfl

/-- Totality for every well-typed state, with canonical FinishE and exact
    eight-word output matching the source reducer applied to those same
    accumulator cells. -/
theorem finishTailCurrent_total (s : Tail) :
    ∃ out : CurrentWide, finishTailCurrent s = .ok out ∧
      ∃ finish : FinishE,
        finishEToCurrent finish = out ∧
        AspisR1CurrentWide.Proof.CanonicalFinish finish ∧
        currentFinishWords out =
          ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
  obtain ⟨finish,hfinish,hcanon,hwords⟩ :=
    AspisR1FinishDotSourceABI.finishFromPush_total (tailToPushState s)
  have hwords' : AspisR1FinishDotSourceABI.finishWords finish =
      ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
    simpa [tailToPushState] using hwords
  refine ⟨finishEToCurrent finish,?_,finish, rfl,hcanon,?_⟩
  · simp only [finishTailCurrent,hfinish,bind_tc_ok]
  · rw [finishEToCurrent_words]
    exact hwords'

/-- Every successful installed operation returns the canonical output and
    exact reducer-residue list from this same input tail state. -/
theorem installed_finish_success_residues (ops : Ops) (s : Tail) (out : CurrentWide)
    (h : (withSourceTailFinish ops).ebyKFinish s = .ok out) :
    ∃ finish : FinishE,
      finishEToCurrent finish = out ∧
      AspisR1CurrentWide.Proof.CanonicalFinish finish ∧
      currentFinishWords out =
        ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
  have hs := finishTailCurrent_total s
  rcases hs with ⟨v,hv,finish,hmap,hcan,hwords⟩
  have heq : v = out := Result.ok.inj (hv.symm.trans (by
    rw [withSourceTailFinish_binding] at h
    exact h))
  have hwordsFinish : currentFinishWords (finishEToCurrent finish) =
      ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
    simpa only [hmap] using hwords
  have hwordsOut : currentFinishWords out =
      ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
    calc
      currentFinishWords out = currentFinishWords v := by rw [heq]
      _ = currentFinishWords (finishEToCurrent finish) := by
        congr 1
        exact hmap.symm
      _ = ((s.c0.sums.val ++ s.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := hwordsFinish
  exact ⟨finish, hmap.trans heq, hcan, hwordsOut⟩

/-- Value-level residue form: each emitted U32 word is the source reducer's
    `x mod P` for the corresponding input U64 accumulator cell. -/
theorem finishTailCurrent_total_residue_values (s : Tail) :
    ∃ out : CurrentWide, finishTailCurrent s = .ok out ∧
      (currentFinishWords out).map (fun w => w.val) =
        ((s.c0.sums.val ++ s.c1.sums.val).map
          (fun x => x.val % AspisV8R17.RawReducer.P)) := by
  obtain ⟨out,hrun,finish,hmap,hcanon,hwords⟩ := finishTailCurrent_total s
  refine ⟨out,hrun,?_⟩
  rw [hwords]
  simp only [List.map_map, Function.comp_def,
    AspisR1EbyKFinish.Proof.word,
    AspisR1CanonicalDotFinish.Proof.canonicalWord_val]

#print axioms finishTailCurrent_total
#print axioms installed_finish_success_residues
#print axioms finishTailCurrent_total_residue_values
end AspisR1FastDotsTailFinishSourceMapV1
