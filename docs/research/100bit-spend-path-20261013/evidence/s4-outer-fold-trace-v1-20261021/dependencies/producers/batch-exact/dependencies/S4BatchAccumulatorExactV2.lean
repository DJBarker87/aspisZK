import FourDotsActualLimbFoldBodyFacadeV2
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FromFnP6GeneratedV2

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Std.Usize
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev Body := AspisR1FastDotsActualLimbFoldBodyFacadeV2.LimbBody
abbrev Loop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1

def batchCell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

def batchFoldCell (sums : Array U64 8#usize) (j : Fin 8) : Nat :=
  AspisR1BatchedFoldSourceStep.fold (batchCell sums j)

private theorem index_success_bound {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

private theorem index_success_eq {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) :
    x = a.val[i.val]'(by
      have hi := index_success_bound a i x h
      simpa [a.property] using hi) := by
  have hi := index_success_bound a i x h
  have hidx : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨y, hspec, hy⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hidx)
  have hxy : x = y := Result.ok.inj (h.symm.trans hspec)
  exact hxy.trans hy

private theorem cell_set (a : Array U64 8#usize) (i : Usize) (x : U64)
    (j : Fin 8) :
    batchCell (a.set i x) j = if i.val = j.val then x.val else batchCell a j := by
  have hj : j.val < (a.val.set i.val x).length := by
    simpa [a.property] using j.isLt
  change ((a.val.set i.val x)[j.val]'hj).val = _
  by_cases heq : i.val = j.val
  · have hself : (a.val.set i.val x)[j.val]'hj = x := by
      have hs := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hj)
      simpa [heq] using hs
    simp [heq, hself]
  · have hother : (a.val.set i.val x)[j.val]'hj =
        a.val[j.val]'(by simpa [a.property] using j.isLt) :=
      List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) heq hj
    simp [heq, hother, batchCell]

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem body_success_exact_update
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize)
    (hbody : Body ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    ∃ (limb : Usize) (x part oldSum newSum : U64)
      (updated : Array U64 8#usize),
      Array.index_usize sums limb = .ok x ∧
      part.val = AspisR1BatchedFoldSourceStep.fold x.val ∧
      Array.index_usize limbs limb = .ok oldSum ∧
      newSum.val = oldSum.val + part.val ∧
      Array.update limbs limb newSum = .ok updated ∧ limbs' = updated ∧
      limb = iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  unfold Body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some limb =>
      obtain ⟨x, hread, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨low, hand, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨high, hshift, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨part, hfoldAdd, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨oldSum, hreadOld, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨newSum, hadd, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨updated, hupdate, hfinal⟩ := bind_success _ _ _ hrest
      have hiterPair : (iter1, updated) = (iter', limbs') :=
        ControlFlow.cont.inj (Result.ok.inj hfinal)
      have hiter : iter1 = iter' := congrArg Prod.fst hiterPair
      have hupdated : updated = limbs' := congrArg Prod.snd hiterPair
      have hflush : BatchedWeightsFlushPrimitiveV2.generatedFlush x = .ok part := by
        unfold BatchedWeightsFlushPrimitiveV2.generatedFlush
        simp only [hand, hshift, bind_tc_ok, hfoldAdd]
      obtain ⟨folded, hfolded, hfoldValue⟩ :=
        BatchedWeightsFlushPrimitiveV2.generatedFlush_success x
      have hfoldedEq : folded = part := Result.ok.inj (hfolded.symm.trans hflush)
      have hpartValue : part.val = AspisR1BatchedFoldSourceStep.fold x.val := by
        simpa [hfoldedEq] using hfoldValue
      have hnewValue : newSum.val = oldSum.val + part.val := by
        have he := UScalar.add_equiv oldSum part
        rw [hadd] at he
        exact he.2.1
      have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
        intro x
        rfl
      have hltSpec : ∀ a b : Usize,
          core.cmp.PartialOrdUsize.lt a b = .ok (decide (a.val < b.val)) := by
        intros
        rfl
      have hiterData : limb = iter.start ∧ iter.start.val < iter.end.val ∧
          iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
        have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
          (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          hclone hltSpec iter
        rw [hnext, WP.spec_ok] at hspec
        by_cases hlt : iter.start.val < iter.end.val
        · simp only [hlt, ↓reduceIte] at hspec
          rcases hspec with ⟨⟨hopt, hadvance⟩, hend⟩
          subst iter'
          exact ⟨Option.some.inj hopt, hlt, hadvance, hend⟩
        · simp only [hlt, ↓reduceIte] at hspec
          rcases hspec with ⟨⟨hnone, _⟩, _⟩
          cases hnone
      exact ⟨limb, x, part, oldSum, newSum, updated,
        hread, hpartValue, hreadOld, hnewValue, hupdate, hupdated.symm,
        hiterData.1, hiterData.2.1, hiterData.2.2.1, hiterData.2.2.2⟩

private def batchLimbStep (ops : Ops) (sums : Array U64 8#usize) :
    (Range × Array U64 8#usize) →
      Result (ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)) :=
  fun st => Body ops sums st.1 st.2

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok flow =>
      cases flow with
      | done result =>
          simp only [hs, bind_tc_ok] at h
          have heq : result = out := Result.ok.inj h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp only [hs, bind_tc_ok] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private theorem body_done_exhausted
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize)
    (hbody : Body ops sums iter limbs = .ok (.done out)) :
    out = limbs ∧ iter.end.val ≤ iter.start.val := by
  unfold Body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      have hout : out = limbs := by
        change Result.ok (ControlFlow.done limbs) = Result.ok (ControlFlow.done out) at hrest
        exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hopt, _⟩, _⟩
        cases hopt
      · exact ⟨hout, by omega⟩
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private def AccumulatorInvariant (iter : Range) (sums initial limbs : Array U64 8#usize) : Prop :=
  ∀ i : Fin 8,
    (i.val < iter.start.val → batchCell limbs i = batchCell initial i + batchFoldCell sums i) ∧
    (iter.start.val ≤ i.val → batchCell limbs i = batchCell initial i)

private theorem accumulator_loop_exact_aux
    (ops : Ops) (sums initial : Array U64 8#usize) :
    ∀ (m : Nat) (iter : Range) (limbs out : Array U64 8#usize),
      iter.end.val - iter.start.val = m →
      iter.end.val = 8 →
      AccumulatorInvariant iter sums initial limbs →
      Loop ops iter limbs sums = .ok out →
      ∀ i : Fin 8, batchCell out i = batchCell initial i + batchFoldCell sums i := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro iter limbs out hmeasure hend hinv hloop i
      have hcore : Aeneas.Std.loop (batchLimbStep ops sums) (iter, limbs) = .ok out := by
        change Aeneas.Std.loop (batchLimbStep ops sums) (iter, limbs) = .ok out
        exact hloop
      rcases loop_success_cases (batchLimbStep ops sums) (iter, limbs) out hcore with
        hdone | ⟨stateNext, hcont, htail⟩
      · have hbody : Body ops sums iter limbs = .ok (.done out) := by
          simpa [batchLimbStep] using hdone
        obtain ⟨hout, hexhaust⟩ := body_done_exhausted ops sums iter limbs out hbody
        subst out
        have hi : i.val < iter.start.val := by
          have hi := i.isLt
          omega
        exact (hinv i).1 hi
      · rcases stateNext with ⟨iter', limbs'⟩
        have hbody : Body ops sums iter limbs = .ok (.cont (iter', limbs')) := by
          simpa [batchLimbStep] using hcont
        obtain ⟨limb,x,part,oldSum,newSum,updated,hread,hpart,hreadOld,hnew,hupdate,hupdated,
          hlimbEq,hlt,hnextStart,hnextEnd⟩ :=
          body_success_exact_update ops sums iter iter' limbs limbs' hbody
        have hidxSum : limb.val < 8 := by
          have hb := index_success_bound sums limb x hread
          simpa [sums.property] using hb
        have hidxOld : limb.val < 8 := by
          have hb := index_success_bound limbs limb oldSum hreadOld
          simpa [limbs.property] using hb
        let j : Fin 8 := ⟨limb.val, hidxSum⟩
        have hlimbval : limb.val = iter.start.val := congrArg (fun x : Usize => x.val) hlimbEq
        have hjval : j.val = limb.val := rfl
        have hjStart : iter.start.val ≤ j.val := by
          rw [hjval, ← hlimbval]
        have holdInitial : batchCell limbs j = batchCell initial j := (hinv j).2 hjStart
        have hsumRead : x.val = batchCell sums j := by
          have heq := index_success_eq sums limb x hread
          simpa [batchCell, j] using congrArg UScalar.val heq
        have hpartCell : part.val = batchFoldCell sums j := by
          rw [hpart, hsumRead]
          rfl
        have holdRead : oldSum.val = batchCell limbs j := by
          have heq := index_success_eq limbs limb oldSum hreadOld
          simpa [batchCell, j] using congrArg UScalar.val heq
        have hnewFold : newSum.val = batchCell initial j + batchFoldCell sums j := by
          rw [hnew, holdRead, holdInitial, hpartCell]
        have hupdateSet : Array.update limbs limb newSum = .ok (limbs.set limb newSum) := by
          obtain ⟨u, hu, hset⟩ := WP.spec_imp_exists
            (Array.update_spec limbs limb newSum (by simpa [limbs.property] using hidxOld))
          simpa only [hset] using hu
        have hupdatedEq : updated = limbs.set limb newSum :=
          Result.ok.inj (hupdate.symm.trans hupdateSet)
        have hlimbsEq : limbs' = limbs.set limb newSum := hupdated.trans hupdatedEq
        have hinvNext : AccumulatorInvariant iter' sums initial limbs' := by
          intro k
          constructor
          · intro hk
            have hkStart : k.val < iter.start.val + 1 := by rw [hnextStart] at hk; exact hk
            by_cases heq : k.val = limb.val
            · have heqj : k.val = j.val := calc
                k.val = limb.val := heq
                _ = j.val := hjval.symm
              have : k = j := Fin.ext heqj
              subst k
              have hlimbEqJ : limb.val = j.val := hjval.symm
              simpa [hlimbsEq, cell_set, hlimbEqJ] using hnewFold
            · have hbefore : k.val < iter.start.val := by omega
              have hunchanged : batchCell (limbs.set limb newSum) k = batchCell limbs k := by
                have hne : limb.val ≠ k.val := Ne.symm heq
                simp [cell_set, hne]
              rw [hlimbsEq, hunchanged]
              exact (hinv k).1 hbefore
          · intro hk
            have hkStart : iter.start.val + 1 ≤ k.val := by rw [hnextStart] at hk; exact hk
            have hne : limb.val ≠ k.val := by rw [hlimbval]; omega
            have hunchanged : batchCell (limbs.set limb newSum) k = batchCell limbs k := by
              simp [cell_set, hne]
            rw [hlimbsEq, hunchanged]
            exact (hinv k).2 (by omega)
        have hmeasure' : iter'.end.val - iter'.start.val = iter.end.val - iter.start.val - 1 := by
          rw [hnextEnd, hnextStart]
          omega
        have hdecrease : iter'.end.val - iter'.start.val < m := by rw [hmeasure']; omega
        have hend' : iter'.end.val = 8 := by rw [hnextEnd, hend]
        have htail' := ih (iter'.end.val - iter'.start.val) hdecrease iter' limbs' out rfl hend' hinvNext htail i
        exact htail'

theorem actual_loop0_loop1_success_exact_batch_values
    (ops : Ops) (sums initial out : Array U64 8#usize)
    (h : Loop ops { start := 0#usize, «end» := 8#usize }
      initial sums = .ok out) :
    ∀ i : Fin 8, batchCell out i = batchCell initial i + batchFoldCell sums i := by
  have hinv : AccumulatorInvariant { start := 0#usize, «end» := 8#usize }
      sums initial initial := by
    intro i
    constructor
    · intro hi
      have hi0 : i.val < 0 := by
        change i.val < (0#usize).val at hi
        simpa using hi
      exact False.elim (Nat.not_lt_zero _ hi0)
    · intro _
      rfl
  exact accumulator_loop_exact_aux ops sums initial 8
    { start := 0#usize, «end» := 8#usize }
    initial out (by rfl) (by rfl) hinv h

#print axioms body_success_exact_update
#print axioms actual_loop0_loop1_success_exact_batch_values
end AspisR1FromFnP6GeneratedV2
