import Aeneas
import Query31ScanTypesOnly
import AspisV8R19.Q22WordScan
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ExplicitScanBody

abbrev CurrentScan := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan

/-- The five Std boundaries used by the extracted scan-loop body.  They are
    parameters, not generated external axioms. -/
structure StdOps (Iter : Type) where
  iterNext : Iter → Result (Option Std.U32 × Iter)
  usizeAdd : Std.Usize → Std.Usize → Result Std.Usize
  readPrefix : Array Std.U32 22#usize → Std.Usize → Result (Slice Std.U32)
  contains : Slice Std.U32 → Std.U32 → Result Bool
  update : Array Std.U32 22#usize → Std.Usize → Std.U32 → Result (Array Std.U32 22#usize)


/-- The four pure/container boundaries use the actual typed Aeneas Std
    operations.  Iterator advancement remains explicit because the generated
    external iterator representation is intentionally abstract here. -/
def stdOps {Iter : Type} (next : Iter → Result (Option Std.U32 × Iter)) : StdOps Iter :=
  { iterNext := next
    usizeAdd := fun x y => x + y
    readPrefix := fun a n =>
      core.array.Array.index
        (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32))
        a { «end» := n }
    contains := core.slice.Slice.contains core.cmp.PartialEqU32
    update := fun a i x => Array.update a i x }

/-- Source-shaped copy of QueryScan.scan_loop.body.  The declaration checker in
    this packet pins the current and prior generated source bodies to this
    operational sequence; each Std operation is supplied explicitly. -/
def body {Iter : Type} (ops : StdOps Iter) (iter : Iter) (s : CurrentScan) :
    Result (ControlFlow ((Iter × CurrentScan)) (CurrentScan × Option Bool)) := do
  let (o, iter1) ← ops.iterNext iter
  match o with
  | none => ok (ControlFlow.done (s, some false))
  | some candidate =>
    if s.accepted_len = 22#usize then
      ok (ControlFlow.done (s, none))
    else if s.draws = 64#usize then
      ok (ControlFlow.done (s, none))
    else
      let i ← ops.usizeAdd s.draws 1#usize
      let sl ← ops.readPrefix s.accepted s.accepted_len
      let b ← ops.contains sl candidate
      if b then
        ok (ControlFlow.cont (iter1, { s with draws := i }))
      else
        let a ← ops.update s.accepted s.accepted_len candidate
        let i1 ← ops.usizeAdd s.accepted_len 1#usize
        ok (ControlFlow.cont (iter1, { accepted := a, accepted_len := i1, draws := i }))



def acceptedPrefix (s : CurrentScan) : List Nat :=
  (s.accepted.val.take s.accepted_len.val).map (fun x => x.val)

def q22StateOf (s : CurrentScan) : AspisV8R19.Q22WordScan.ScanState :=
  ⟨acceptedPrefix s, s.draws.val⟩

private theorem take_set_succ {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) (x : α) :
    (xs.set i x).take (i + 1) = xs.take i ++ [x] := by
  induction i generalizing xs with
  | zero => cases xs with | nil => simp at hi | cons a tail => simp
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons a tail =>
          have hi' : i < tail.length := by simp at hi; omega
          simp [ih tail hi']

private theorem array_update_success_val {α : Type} {n : Usize}
    (v : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    ∃ a : Array α n, Array.update v i x = .ok a ∧
      a.val = v.val.set i.val x := by
  have hidx : i.val < v.val.length := by simpa [v.property] using hi
  let a : Array α n := ⟨v.val.set i.val x, by simp [List.length_set, v.property]⟩
  refine ⟨a, ?_, rfl⟩
  unfold Array.update
  change (match v.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some _ => Result.ok a) = Result.ok a
  rw [List.getElem?_eq_getElem hidx]

theorem q22_state_fresh_update
    (s : CurrentScan) (candidate : Std.U32) (a : Array Std.U32 22#usize)
    (lenNext drawNext : Std.Usize)
    (hupdate : s.accepted.update s.accepted_len candidate = ok a)
    (hbound : s.accepted_len.val < s.accepted.val.length)
    (hlenval : lenNext.val = s.accepted_len.val + 1)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    q22StateOf { s with accepted := a, accepted_len := lenNext, draws := drawNext } =
      ⟨acceptedPrefix s ++ [candidate.val], s.draws.val + 1⟩ := by
  have hbound' : s.accepted_len.val < (22#usize).val := by
    simpa [s.accepted.property] using hbound
  obtain ⟨a0, hupdate0, hset⟩ := array_update_success_val s.accepted s.accepted_len candidate hbound'
  have haa : a0 = a := Result.ok.inj (hupdate0.symm.trans hupdate)
  have hseta : a.val = s.accepted.val.set s.accepted_len.val candidate := by
    simpa [haa] using hset
  change (⟨(a.val.take lenNext.val).map (fun x => x.val), drawNext.val⟩ :
      AspisV8R19.Q22WordScan.ScanState) =
    ⟨acceptedPrefix s ++ [candidate.val], s.draws.val + 1⟩
  simp only [AspisV8R19.Q22WordScan.ScanState.mk.injEq]
  constructor
  · rw [hseta, hlenval, take_set_succ _ _ hbound]
    simp [acceptedPrefix]
  · exact hdrawval

/-- The prior Q22 list contract's exact one-word fresh transition. -/
theorem q22_fresh_transition (state : AspisV8R19.Q22WordScan.ScanState)
    (word : Nat) (hlen : state.accepted.length < 22)
    (hdraw : state.draws < 64) (hfresh : word ∉ state.accepted) :
    AspisV8R19.Q22WordScan.scan state [word] =
      ({ accepted := state.accepted ++ [word], draws := state.draws + 1 }, false) := by
  have hstop : ¬ (state.accepted.length = 22 ∨ state.draws = 64) := by omega
  simp [AspisV8R19.Q22WordScan.scan, hstop,
    AspisV8R19.Q22WordScan.keep, hfresh]

/-- The prior Q22 list contract's duplicate transition. -/
theorem q22_duplicate_transition (state : AspisV8R19.Q22WordScan.ScanState)
    (word : Nat) (hlen : state.accepted.length < 22)
    (hdraw : state.draws < 64) (hmember : word ∈ state.accepted) :
    AspisV8R19.Q22WordScan.scan state [word] =
      (state.accepted |> fun accepted =>
        ({ accepted, draws := state.draws + 1 } : AspisV8R19.Q22WordScan.ScanState), false) := by
  have hstop : ¬ (state.accepted.length = 22 ∨ state.draws = 64) := by omega
  simp [AspisV8R19.Q22WordScan.scan, hstop,
    AspisV8R19.Q22WordScan.keep, hmember]

/-- Fresh-candidate step law, with the exact source call results exposed. -/
theorem fresh_step
    {Iter : Type} (ops : StdOps Iter) (iter iter1 : Iter) (s : CurrentScan)
    (candidate : Std.U32) (drawNext lenNext : Std.Usize)
    (sl : Slice Std.U32) (a : Array Std.U32 22#usize)
    (hnext : ops.iterNext iter = .ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ 22#usize)
    (hnotcap : s.draws ≠ 64#usize)
    (hdraw : ops.usizeAdd s.draws 1#usize = .ok drawNext)
    (hprefix : ops.readPrefix s.accepted s.accepted_len = .ok sl)
    (hcontains : ops.contains sl candidate = .ok false)
    (hupdate : ops.update s.accepted s.accepted_len candidate = .ok a)
    (hlen : ops.usizeAdd s.accepted_len 1#usize = .ok lenNext) :
    body ops iter s = .ok (.cont (iter1,
      { accepted := a, accepted_len := lenNext, draws := drawNext })) := by
  simp [body, hnext, hnotfull, hnotcap, hdraw, hprefix, hcontains, hupdate, hlen]

/-- Duplicate-candidate step law, with no update call. -/
theorem duplicate_step
    {Iter : Type} (ops : StdOps Iter) (iter iter1 : Iter) (s : CurrentScan)
    (candidate : Std.U32) (drawNext : Std.Usize) (sl : Slice Std.U32)
    (hnext : ops.iterNext iter = .ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ 22#usize)
    (hnotcap : s.draws ≠ 64#usize)
    (hdraw : ops.usizeAdd s.draws 1#usize = .ok drawNext)
    (hprefix : ops.readPrefix s.accepted s.accepted_len = .ok sl)
    (hcontains : ops.contains sl candidate = .ok true) :
    body ops iter s = .ok (.cont (iter1, { s with draws := drawNext })) := by
  simp [body, hnext, hnotfull, hnotcap, hdraw, hprefix, hcontains]


/-- One-step source-body to Q22 recurrence bridge.  Every source operation is
    an explicit premise; `q22_state_fresh_update` connects the actual returned
    array/length/draw values to the recurrence state. -/
theorem fresh_step_q22
    {Iter : Type} (ops : StdOps Iter) (iter iter1 : Iter) (s : CurrentScan)
    (candidate : Std.U32) (drawNext lenNext : Std.Usize)
    (sl : Slice Std.U32) (a : Array Std.U32 22#usize)
    (hnext : ops.iterNext iter = .ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ 22#usize)
    (hnotcap : s.draws ≠ 64#usize)
    (hdraw : ops.usizeAdd s.draws 1#usize = .ok drawNext)
    (hprefix : ops.readPrefix s.accepted s.accepted_len = .ok sl)
    (hcontains : ops.contains sl candidate = .ok false)
    (hupdate : ops.update s.accepted s.accepted_len candidate = .ok a)
    (hupdateStd : s.accepted.update s.accepted_len candidate = .ok a)
    (hlen : ops.usizeAdd s.accepted_len 1#usize = .ok lenNext)
    (hmodelLen : (q22StateOf s).accepted.length < 22)
    (hmodelDraw : (q22StateOf s).draws < 64)
    (hfresh : candidate.val ∉ acceptedPrefix s)
    (hbound : s.accepted_len.val < s.accepted.val.length)
    (hlenval : lenNext.val = s.accepted_len.val + 1)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    body ops iter s = .ok (.cont (iter1,
      { accepted := a, accepted_len := lenNext, draws := drawNext })) ∧
    AspisV8R19.Q22WordScan.scan (q22StateOf s) [candidate.val] =
      (q22StateOf { accepted := a, accepted_len := lenNext, draws := drawNext }, false) := by
  have hbody := fresh_step ops iter iter1 s candidate drawNext lenNext sl a
    hnext hnotfull hnotcap hdraw hprefix hcontains hupdate hlen
  have hstate := q22_state_fresh_update s candidate a lenNext drawNext
    hupdateStd hbound hlenval hdrawval
  have hscan := q22_fresh_transition (q22StateOf s) candidate.val
    hmodelLen hmodelDraw hfresh
  refine ⟨hbody, ?_⟩
  rw [hscan]
  exact congrArg (fun q => (q, false)) hstate.symm

/-- Duplicate-step bridge to the Q22 recurrence.  The accepted prefix is
    unchanged and only the draw counter advances. -/
theorem duplicate_step_q22
    {Iter : Type} (ops : StdOps Iter) (iter iter1 : Iter) (s : CurrentScan)
    (candidate : Std.U32) (drawNext : Std.Usize) (sl : Slice Std.U32)
    (hnext : ops.iterNext iter = .ok (some candidate, iter1))
    (hnotfull : s.accepted_len ≠ 22#usize)
    (hnotcap : s.draws ≠ 64#usize)
    (hdraw : ops.usizeAdd s.draws 1#usize = .ok drawNext)
    (hprefix : ops.readPrefix s.accepted s.accepted_len = .ok sl)
    (hcontains : ops.contains sl candidate = .ok true)
    (hmodelLen : (q22StateOf s).accepted.length < 22)
    (hmodelDraw : (q22StateOf s).draws < 64)
    (hmember : candidate.val ∈ acceptedPrefix s)
    (hdrawval : drawNext.val = s.draws.val + 1) :
    body ops iter s = .ok (.cont (iter1, { s with draws := drawNext })) ∧
    AspisV8R19.Q22WordScan.scan (q22StateOf s) [candidate.val] =
      (q22StateOf { s with draws := drawNext }, false) := by
  have hbody := duplicate_step ops iter iter1 s candidate drawNext sl
    hnext hnotfull hnotcap hdraw hprefix hcontains
  have hscan := q22_duplicate_transition (q22StateOf s) candidate.val
    hmodelLen hmodelDraw hmember
  refine ⟨hbody, ?_⟩
  rw [hscan]
  simp [q22StateOf, acceptedPrefix, hdrawval]

#print axioms stdOps
#print axioms fresh_step_q22
#print axioms duplicate_step_q22
#print axioms q22_state_fresh_update
#print axioms q22_fresh_transition
#print axioms q22_duplicate_transition
#print axioms fresh_step
#print axioms duplicate_step
end Query31ExplicitScanBody
