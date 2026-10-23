import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3DoubleCanonicalV1
import S9ConstructorV3Loop1CellCanonicalV1
import S9LoopInvariantPropertyV1
import S9PairArrayUpdateCanonicalV1
import S9CandidateFoldMapPrimitivesV1
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1S9ConstructorV3Loop2InnerCanonicalV1

abbrev Q := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev ProbeQ := AspisR1S9ActualQM31WrappingMapV1.ProbeQM
abbrev CanQ := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev Cell := Array Q (4#usize)
abbrev Row := Array Cell (5#usize)
abbrev Factors := Array Row (5#usize)
abbrev R := core.ops.range.Range Std.Usize

def toProbeQ (x : Q) : ProbeQ :=
  AspisR1S9ConstructorV3QMMulCanonicalV1.toProbe x

def mapCells (a : Cell) : Array ProbeQ (4#usize) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray toProbeQ a

def mapRow (a : Row) : Array (Array ProbeQ (4#usize)) (5#usize) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray mapCells a

def mapFactors (a : Factors) : Array (Array (Array ProbeQ (4#usize)) (5#usize)) (5#usize) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray mapRow a

def CellsCanonical (a : Array ProbeQ (4#usize)) : Prop :=
  ∀ (j : Std.Usize) (v : ProbeQ),
    Array.index_usize a j = .ok v → CanQ v

def RowsCanonical (row : Array (Array ProbeQ (4#usize)) (5#usize)) : Prop :=
  ∀ (j : Std.Usize) (cell : Array ProbeQ (4#usize)),
    Array.index_usize row j = .ok cell → CellsCanonical cell

def FactorsCanonical (a : Factors) : Prop :=
  ∀ (i : Std.Usize) (row : Array (Array ProbeQ (4#usize)) (5#usize)),
    Array.index_usize (mapFactors a) i = .ok row → RowsCanonical row

theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

theorem index_mut_read
    {A : Type} {N : Std.Usize} (a : Array A N) (i : Std.Usize)
    (old : A) (back : A → Array A N)
    (h : Array.index_mut_usize a i = .ok (old, back)) :
    Array.index_usize a i = .ok old := by
  unfold Array.index_mut_usize at h
  cases hr : Array.index_usize a i with
  | ok x =>
      simp only [hr, bind_tc_ok] at h
      have he := Result.ok.inj h
      have hx : x = old := congrArg Prod.fst he
      rw [← hx]
  | fail e => simp only [hr, bind_tc_fail] at h; cases h
  | div => simp only [hr, bind_tc_div] at h; cases h

theorem index_mut_bound
    {A : Type} {N : Std.Usize} (a : Array A N) (i : Std.Usize)
    (old : A) (back : A → Array A N)
    (h : Array.index_mut_usize a i = .ok (old, back)) : i.val < N.val :=
  index_success_bound a i old (index_mut_read a i old back h)

theorem index_mut_back_set
    {A : Type} {N : Std.Usize} (a : Array A N) (i : Std.Usize)
    (old : A) (back : A → Array A N)
    (hbound : i.val < N.val)
    (h : Array.index_mut_usize a i = .ok (old, back)) :
    back = fun v => a.set i v := by
  have hlen : i.val < a.length := by simpa only [a.property] using hbound
  obtain ⟨pair, hspec, hpost⟩ :=
    WP.spec_imp_exists (Array.index_mut_usize_spec a i hlen)
  rcases pair with ⟨old', back'⟩
  rcases hpost with ⟨_, hback'⟩
  have heq : (old', back') = (old, back) := Result.ok.inj (hspec.symm.trans h)
  have hsnd := congrArg Prod.snd heq
  exact hsnd.symm.trans hback'

theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem next_some_progress (iter iterNext : R) (d : Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some d, iterNext)) :
    iter.start.val < iter.end.val ∧ d = iter.start ∧
      iterNext.start.val = iter.start.val + 1 ∧ iterNext.end = iter.end := by
  have hlt : iter.start.val < iter.end.val := by
    by_contra hge
    have hnoneSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) iter (by omega)
    obtain ⟨pair, hrun, hpost⟩ := WP.spec_imp_exists hnoneSpec
    rcases pair with ⟨opt, next⟩
    rcases hpost with ⟨hopt, hiter⟩
    subst opt
    have hnextNone : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (none, iter) := by simpa [hiter] using hrun
    rw [hnext] at hnextNone
    cases hnextNone
  have hsomeSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter hlt
  obtain ⟨pair, hrun, hpost⟩ := WP.spec_imp_exists hsomeSpec
  rcases pair with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hstart, hend⟩
  have heq : (opt, next) = (some d, iterNext) := Result.ok.inj (hrun.symm.trans hnext)
  have hopt' : opt = some d := congrArg Prod.fst heq
  have hnext' : next = iterNext := congrArg Prod.snd heq
  have hdEq : some iter.start = some d := hopt.symm.trans hopt'
  have hd : d = iter.start := by injection hdEq with hd; exact hd.symm
  have hstart' : iterNext.start.val = iter.start.val + 1 := by
    rw [← hnext']
    exact hstart
  have hend' : iterNext.end = iter.end := by
    rw [← hnext']
    exact hend
  exact ⟨hlt, hd, hstart', hend'⟩

private def innerBody (k : Std.Usize) :
    (R × Factors × Q) → Result (ControlFlow (R × Factors × Q) Factors) :=
  fun s => AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
    k s.1 s.2.1 s.2.2

/-- Exact continuation of the generated body after its `some d` range result. -/
private def cellTail (k d : Std.Usize) (iter1 : R) (factors : Factors) (x : Q) :
    Result (ControlFlow (R × Factors × Q) Factors) := do
  let y ← AspisR1S9ActualWeightsNewBoxNewV3.double x
  let q ← AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y
  let i ← lift (Std.Usize.wrapping_add 3#usize k)
  let (old, back) ← Array.index_mut_usize factors i
  let rowOut ← Array.update old d
    (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)
  let xNext ← AspisR1S9ActualWeightsNewBoxNewV3.double y
  ok (.cont (iter1, back rowOut, xNext))

private theorem cellTail_success_cont
    (k d : Std.Usize) (iter1 : R) (factors : Factors) (x : Q)
    (cf : ControlFlow (R × Factors × Q) Factors)
    (h : cellTail k d iter1 factors x = .ok cf) :
    ∃ factorsOut xOut, cf = .cont (iter1, factorsOut, xOut) := by
  unfold cellTail at h
  obtain ⟨y, hy, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨q, hq, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨mutPair, hm, h⟩ := bind_success_inv _ _ _ h
  rcases mutPair with ⟨old, back⟩
  change (do
    let rowOut ← Array.update old d
      (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)
    let xNext ← AspisR1S9ActualWeightsNewBoxNewV3.double y
    ok (ControlFlow.cont (iter1, back rowOut, xNext) : ControlFlow (R × Factors × Q) Factors)) = ok cf at h
  obtain ⟨rowOut, hu, h⟩ := bind_success_inv _ _ _ h
  obtain ⟨xNext, hxNext, h⟩ := bind_success_inv _ _ _ h
  exact ⟨back rowOut, xNext, (Result.ok.inj h).symm⟩

private theorem body_cont_has_next
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q)
    (iterNext : R) (factorsNext : Factors) (xNext : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext, factorsNext, xNext))) :
    ∃ d, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some d, iterNext) := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases pair with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors × Q) Factors) =
      ok (ControlFlow.cont (iterNext, factorsNext, xNext) : ControlFlow (R × Factors × Q) Factors) at hrest
    cases hrest
  | some d =>
    change cellTail k d iter1 factors x = ok (.cont (iterNext, factorsNext, xNext)) at hrest
    obtain ⟨factorsOut, xOut, hcf⟩ := cellTail_success_cont
      k d iter1 factors x _ hrest
    have hiter : iterNext = iter1 := congrArg Prod.fst (ControlFlow.cont.inj hcf)
    subst iter1
    exact ⟨d, hnext⟩

private theorem body_done_same_factors
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q) (out : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.done out)) : out = factors := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨pair, hnext, hrest⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases pair with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors × Q) Factors) =
      ok (ControlFlow.done out : ControlFlow (R × Factors × Q) Factors) at hrest
    exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some d =>
    change cellTail k d iter1 factors x = ok (.done out) at hrest
    obtain ⟨factorsOut, xOut, hcf⟩ := cellTail_success_cont
      k d iter1 factors x _ hrest
    cases hcf

def invariant (s : R × Factors × Q) : Prop :=
  s.1.end = 5#usize ∧ FactorsCanonical s.2.1 ∧ CanQ (toProbeQ s.2.2)

def measure (s : R × Factors × Q) : Nat :=
  s.1.end.val - s.1.start.val

private theorem body_cont_preserves
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q)
    (iterNext : R) (factorsNext : Factors) (xNext : Q)
    (hinv : invariant (iter, factors, x))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext, factorsNext, xNext))) :
    invariant (iterNext, factorsNext, xNext) := by
  obtain ⟨d, hnext⟩ := body_cont_has_next k iter factors x iterNext factorsNext xNext hbody
  obtain ⟨hlt, hd, hstart, hend⟩ := next_some_progress iter iterNext d hnext
  have hrowinput : ∀ (i : Std.Usize) (old : Row) (back : Row → Factors),
      Array.index_mut_usize factors i = .ok (old, back) →
      ∀ (j : Std.Usize) (cell : Array ProbeQ (4#usize)),
        Array.index_usize (mapRow old) j = .ok cell → CellsCanonical cell := by
    intro i old back hmut j cell hread
    have hidx := index_mut_read factors i old back hmut
    have hmapped : Array.index_usize (mapFactors factors) i = .ok (mapRow old) := by
      calc
        Array.index_usize (mapFactors factors) i =
            AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapRow
              (Array.index_usize factors i) :=
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result mapRow factors i).symm
        _ = .ok (mapRow old) := by rw [hidx]; rfl
    exact hinv.2.1 i (mapRow old) hmapped j cell hread
  have hdBound : d.val < 5 := by
    have hstartBound : iter.start.val < 5 := by
      rw [hinv.1] at hlt
      simpa using hlt
    simpa [hd] using hstartBound
  obtain ⟨y, q, i, old, back, rowOut, hy, hq, hi, hm, hu, hxNext, hxNextCan,
      hfactorOut, hrowOutCan⟩ :=
    AspisR1S9ConstructorV3Loop1CellCanonicalV1.loop1_body_same_call_cell_row_canonical
      k d iter iterNext factors factorsNext x xNext hnext hbody
      hinv.2.2 hdBound hrowinput
  have hiBound := index_mut_bound factors i old back hm
  have hback := index_mut_back_set factors i old back hiBound hm
  have hfactorOut' : factorsNext = factors.set i rowOut := by
    simpa only [hback] using hfactorOut
  have hlen : i.val < factors.length := by simpa only [factors.property] using hiBound
  obtain ⟨out, hupdate, hout⟩ :=
    WP.spec_imp_exists (Array.update_spec factors i rowOut hlen)
  have hsame : out = factorsNext := by
    calc
      out = factors.set i rowOut := hout
      _ = factorsNext := hfactorOut'.symm
  have hupdate' : Array.update factors i rowOut = .ok factorsNext := by
    rw [hupdate, hsame]
  have hrows := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    mapRow RowsCanonical factors i rowOut factorsNext hiBound hupdate'
    hinv.2.1 hrowOutCan
  refine ⟨?_, hrows, hxNextCan⟩
  rw [hend, hinv.1]

/-- The actual generated four-row loop preserves pointwise canonicality of its
factor rows. Each continuation uses the same successful cell-body execution;
no replacement loop or independent arithmetic witnesses are used. -/
theorem inner_loop_success_preserves
    (k : Std.Usize) (iter : R) (factors : Factors) (x : Q) (out : Factors)
    (hinv : invariant (iter, factors, x))
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
      iter factors k x = .ok out) : FactorsCanonical out := by
  let step : (R × Factors × Q) → Result (ControlFlow (R × Factors × Q) Factors) :=
    innerBody k
  have hdone : ∀ s out, invariant s → step s = .ok (.done out) → FactorsCanonical out := by
    intro s out hs hstep
    rcases s with ⟨iter, factors, x⟩
    have hsame := body_done_same_factors k iter factors x out hstep
    subst out
    exact hs.2.1
  have hcontinue : ∀ s s', invariant s → step s = .ok (.cont s') → invariant s' := by
    intro s s' hs hstep
    rcases s with ⟨iter, factors, x⟩
    rcases s' with ⟨iterNext, factorsNext, xNext⟩
    exact body_cont_preserves k iter factors x iterNext factorsNext xNext hs hstep
  have hdecrease : ∀ s s', step s = .ok (.cont s') → measure s' < measure s := by
    intro s s' hstep
    rcases s with ⟨iter, factors, x⟩
    rcases s' with ⟨iterNext, factorsNext, xNext⟩
    obtain ⟨d, hnext⟩ := body_cont_has_next k iter factors x iterNext factorsNext xNext hstep
    obtain ⟨hlt, _, hstart, hend⟩ := next_some_progress iter iterNext d hnext
    simp only [measure, hstart, hend]
    omega
  have hloop' : Aeneas.Std.loop step (iter, factors, x) = .ok out := by
    change Aeneas.Std.loop (innerBody k) (iter, factors, x) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure invariant FactorsCanonical hdone hcontinue hdecrease
    (iter, factors, x) out hinv hloop'

#print axioms inner_loop_success_preserves

end AspisR1S9ConstructorV3Loop2InnerCanonicalV1
