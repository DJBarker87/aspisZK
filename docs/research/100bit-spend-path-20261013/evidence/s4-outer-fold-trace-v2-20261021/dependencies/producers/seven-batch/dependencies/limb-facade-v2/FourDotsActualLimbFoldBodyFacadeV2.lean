import AspisR1FastDotsCurrent.FunsOpsV4
import BatchedWeightsFlushPrimitiveV2
import AspisR1BatchedFoldSourceStep
import FourDotsActualLimbPrefixStepV2
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualLimbFoldBodyFacadeV2

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Std.Usize
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev LimbBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body
@[irreducible] def LimbLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
abbrev limbCap : Nat := 2^34 - 1
abbrev productCap : Nat := (2^31 - 2)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

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

private theorem limb_body_success_step_data
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize)
    (hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    ∃ limb x part oldSum newSum updated,
      Array.index_usize sums limb = .ok x ∧
      part.val = (AspisR1BatchedFoldSourceStep.fold x.val) ∧
      Array.index_usize limbs limb = .ok oldSum ∧
      UScalar.add oldSum part = .ok newSum ∧
      newSum.val = oldSum.val + part.val ∧
      Array.update limbs limb newSum = .ok updated ∧
      limbs' = updated ∧
      limb = iter.start ∧
      iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  unfold LimbBody at hbody
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
        hread, hpartValue, hreadOld, hadd, hnewValue, hupdate, hupdated.symm,
        hiterData.1, hiterData.2.1, hiterData.2.2.1, hiterData.2.2.2⟩

/-- The emitted body performs the exact Mersenne limb fold on the selected
    batch sum, then adds it to and writes back the same selected accumulator
    cell. The contribution is below `2^34` by the retained R22 fold bound. -/
theorem limb_body_success_fold_bound
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize)
    (hsums : ∀ i : Fin 8, cell sums i ≤ 4 * productCap)
    (batchCount : Nat)
    (hprefix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      cell limbs i ≤ batchCount * limbCap)
    (hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    ∃ (limb : Usize) (x oldSum part newSum : U64)
      (updated : Array U64 8#usize),
      Array.index_usize sums limb = .ok x ∧
      x.val ≤ 4 * productCap ∧
      part.val < 2^34 ∧
      newSum.val ≤ (batchCount + 1) * limbCap ∧
      Array.index_usize limbs limb = .ok oldSum ∧
      Array.update limbs limb newSum = .ok updated ∧ limbs' = updated ∧
      limb = iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  obtain ⟨limb, x, part, oldSum, newSum, updated,
      hread, hpart, hreadOld, hadd, hnew, hupdate, hupdated, hlimbEq,
      hlt, hstart, hend⟩ :=
    limb_body_success_step_data ops sums iter iter' limbs limbs' hbody
  have hlimb : limb.val < 8 := by
    have hi := index_success_bound sums limb x hread
    simpa [sums.property] using hi
  have hxEq := index_success_eq sums limb x hread
  have hsumBound : x.val ≤ 4 * productCap := by
    rw [hxEq]
    exact hsums ⟨limb.val, by simpa using hlimb⟩
  have hfoldBound : AspisR1BatchedFoldSourceStep.fold x.val < 2^34 :=
    AspisR1BatchedFoldSourceStep.fold_lt_two34 (by
      change x.bv.toNat < 2^64
      exact x.bv.isLt)
  have hlimbBound : oldSum.val ≤ batchCount * limbCap := by
    rw [index_success_eq limbs limb oldSum hreadOld]
    have hstart : limb.val = iter.start.val := congrArg UScalar.val hlimbEq
    have hstartle : iter.start.val ≤ limb.val := by rw [hstart]
    exact hprefix ⟨limb.val, by simpa using hlimb⟩ hstartle
  have hnewBound : newSum.val ≤ (batchCount + 1) * limbCap := by
    rw [hnew]
    change oldSum.val + part.val ≤ (batchCount + 1) * limbCap
    rw [hpart]
    have hpartLe : AspisR1BatchedFoldSourceStep.fold x.val ≤ limbCap := by
      unfold limbCap
      omega
    -- The accumulator contains at most `batchCount` prior folded batches;
    -- this actual fold contributes at most one more limb-cap unit.
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hsumVal : part.val = AspisR1BatchedFoldSourceStep.fold x.val := hpart
  have hpartBound : part.val < 2^34 := by rw [hsumVal]; exact hfoldBound
  exact ⟨limb, x, oldSum, part, newSum, updated, hread, hsumBound, hpartBound,
    hnewBound, hreadOld, hupdate, hupdated, hlimbEq, hlt, hstart, hend⟩

#print axioms limb_body_success_fold_bound

/-- The same emitted successful fold preserves the source reducer residue. -/
theorem limb_body_success_fold_residue
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize)
    (hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    ∃ limb x, ∃ (part : U64), Array.index_usize sums limb = .ok x ∧
      part.val = AspisR1BatchedFoldSourceStep.fold x.val ∧
      part.val % AspisR1BatchedFoldSourceStep.modulus =
        x.val % AspisR1BatchedFoldSourceStep.modulus := by
  obtain ⟨limb, x, part, oldSum, newSum, updated,
      hread, hpart, _hreadOld, _hadd, _hnew, _hupdate, _hupdated,
      _hlimbEq, _hlt, _hstart, _hend⟩ :=
    limb_body_success_step_data ops sums iter iter' limbs limbs' hbody
  refine ⟨limb, x, part, hread, hpart, ?_⟩
  rw [hpart]
  exact AspisR1BatchedFoldSourceStep.fold_preserves_mod x.val

#print axioms limb_body_success_fold_residue

private def limbStep (ops : Ops) (sums : Array U64 8#usize) :
    (Range × Array U64 8#usize) →
      Result (ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)) :=
  fun state => LimbBody ops sums state.1 state.2

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

private theorem limb_body_done_eq
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize)
    (hbody : LimbBody ops sums iter limbs = .ok (.done out)) : out = limbs := by
  unfold LimbBody at hbody
  obtain ⟨⟨o, _iter1⟩, _hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private theorem limb_body_preserves_bounds
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize) (batchCount : Nat)
    (hsums : ∀ i : Fin 8, cell sums i ≤ 4 * productCap)
    (hglobal : ∀ i : Fin 8, cell limbs i ≤ (batchCount + 1) * limbCap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      cell limbs i ≤ batchCount * limbCap)
    (hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    (∀ i : Fin 8, cell limbs' i ≤ (batchCount + 1) * limbCap) ∧
    (∀ i : Fin 8, iter'.start.val ≤ i.val → cell limbs' i ≤ batchCount * limbCap) ∧
    iter.start.val < iter.end.val ∧
    iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  obtain ⟨limb, x, oldSum, part, newSum, updated,
      _hread, _hxbound, _hpartlt, hnewbound, hreadOld, hupdate, hupdated,
      hlimbEq, hlt, hnextStart, hnextEnd⟩ :=
    limb_body_success_fold_bound ops sums iter iter' limbs limbs' hsums
      batchCount hsuffix hbody
  have hidx : limb.val < limbs.val.length := by
    have hi := index_success_bound limbs limb oldSum hreadOld
    simpa [limbs.property] using hi
  have hupdateSet : Array.update limbs limb newSum = .ok (limbs.set limb newSum) := by
    obtain ⟨u, hu, hset⟩ := WP.spec_imp_exists (Array.update_spec limbs limb newSum hidx)
    simpa only [hset] using hu
  have hupdatedEq : updated = limbs.set limb newSum :=
    Result.ok.inj (hupdate.symm.trans hupdateSet)
  have hlimbsEq : limbs' = limbs.set limb newSum := hupdated.trans hupdatedEq
  have hcap : 0 < limbCap := by norm_num [limbCap]
  have hbasePlus : ∀ i : Fin 8, cell limbs i ≤ (batchCount + 1) * limbCap := hglobal
  have hglobalNext : ∀ i : Fin 8, cell limbs' i ≤ (batchCount + 1) * limbCap := by
    have hs := AspisR1FastDotsActualLimbPrefixStepV2.set_preserves_pointwise_bound
      limbs limb newSum ((batchCount + 1) * limbCap) hbasePlus hnewbound
    intro i
    rw [hlimbsEq]
    exact hs i
  have hsuffixNext : ∀ i : Fin 8, iter'.start.val ≤ i.val →
      cell limbs' i ≤ batchCount * limbCap := by
    intro i hi
    have hlimbNe : limb.val ≠ i.val := by
      have hstart : limb.val = iter.start.val := congrArg UScalar.val hlimbEq
      rw [hnextStart] at hi
      rw [hstart]
      omega
    have hsetLen : i.val < (limbs.val.set limb.val newSum).length := by
      simpa [limbs.property] using i.isLt
    have horigLen : i.val < limbs.val.length := by
      simpa [limbs.property] using i.isLt
    have hsame : cell limbs' i = cell limbs i := by
      unfold cell
      rw [hlimbsEq]
      change ((limbs.val.set limb.val newSum)[i.val]'hsetLen).val =
        (limbs.val[i.val]'horigLen).val
      rw [List.getElem_set_ne (l := limbs.val) (i := limb.val) (j := i.val)
        hlimbNe hsetLen]
    rw [hsame]
    exact hsuffix i (by omega)
  exact ⟨hglobalNext, hsuffixNext, hlt, hnextStart, hnextEnd⟩

/-- The actual generated eight-limb fold loop preserves the accumulator
    envelope. Each visited coordinate adds one bounded reducer result, and
    the range iterator advances monotonically, so unvisited coordinates keep
    the prior-batch bound. -/
private def LimbGlobalBound (limbs : Array U64 8#usize) (bound : Nat) : Prop :=
  ∀ i : Fin 8, cell limbs i ≤ bound

private def LimbFutureBound (iter : Range) (limbs : Array U64 8#usize)
    (bound : Nat) : Prop :=
  ∀ i : Fin 8, iter.start.val ≤ i.val → cell limbs i ≤ bound

private theorem limb_loop_success_batch_bound_aux
    (ops : Ops) (sums : Array U64 8#usize) (batchCount : Nat)
    (hsums : ∀ i : Fin 8, cell sums i ≤ 4 * productCap) :
    ∀ (m : Nat) (iter : Range) (limbs out : Array U64 8#usize),
      iter.end.val - iter.start.val = m →
      LimbGlobalBound limbs ((batchCount + 1) * limbCap) →
      LimbFutureBound iter limbs (batchCount * limbCap) →
      LimbLoop ops iter limbs sums = .ok out →
      LimbGlobalBound out ((batchCount + 1) * limbCap) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro iter limbs out hmeasure hglobal hsuffix hloop
      unfold LimbLoop at hloop
      change Aeneas.Std.loop (limbStep ops sums) (iter, limbs) = .ok out at hloop
      rcases loop_success_cases (limbStep ops sums) (iter, limbs) out hloop with
        hdone | ⟨stateNext, hcont, htail⟩
      · have hbody : LimbBody ops sums iter limbs = .ok (.done out) := by
          simpa [limbStep] using hdone
        have hout := limb_body_done_eq ops sums iter limbs out hbody
        subst out
        intro i
        exact hglobal i
      · rcases stateNext with ⟨iter', limbs'⟩
        have hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs')) := by
          simpa [limbStep] using hcont
        have hstep := limb_body_preserves_bounds ops sums iter iter' limbs limbs'
          batchCount hsums hglobal hsuffix hbody
        have hglobalNext := hstep.1
        have hsuffixNext := hstep.2.1
        have hlt := hstep.2.2.1
        have hnextStart := hstep.2.2.2.1
        have hnextEnd := hstep.2.2.2.2
        have hdecrease : iter.end.val - iter'.start.val < m := by
          rw [hnextStart, ← hmeasure]
          omega
        have hmeasure' : iter'.end.val - iter'.start.val =
            iter.end.val - iter'.start.val := by
          rw [hnextEnd]
        have htail' : LimbLoop ops iter' limbs' sums = .ok out := by
          unfold LimbLoop
          exact htail
        exact ih _ hdecrease iter' limbs' out hmeasure' hglobalNext hsuffixNext htail'

theorem limb_loop_success_batch_bound
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize) (batchCount : Nat)
    (hsums : ∀ i : Fin 8, cell sums i ≤ 4 * productCap)
    (hglobal : LimbGlobalBound limbs (batchCount * limbCap))
    (hsuffix : LimbFutureBound iter limbs (batchCount * limbCap))
    (hloop : LimbLoop ops iter limbs sums = .ok out) :
    LimbGlobalBound out ((batchCount + 1) * limbCap) := by
  have hcap : 0 < limbCap := by norm_num [limbCap]
  have hglobalTarget : LimbGlobalBound limbs ((batchCount + 1) * limbCap) := by
    intro i
    have hle : batchCount * limbCap ≤ (batchCount + 1) * limbCap := by nlinarith
    exact le_trans (hglobal i) hle
  exact limb_loop_success_batch_bound_aux ops sums batchCount hsums _ iter limbs out rfl
    hglobalTarget hsuffix hloop

#print axioms limb_loop_success_batch_bound


/-- Public source-facing facade: the opaque loop alias is internalized here,
    while callers receive the ordinary per-coordinate bound and pass the
    actual generated loop call. -/
theorem limb_loop_generated_call_batch_bound
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize) (batchCount : Nat)
    (hsums : ∀ i : Fin 8, cell sums i ≤ 4 * productCap)
    (hglobal : ∀ i : Fin 8, cell limbs i ≤ batchCount * limbCap)
    (hloop : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
      ops iter limbs sums = .ok out) :
    ∀ i : Fin 8, cell out i ≤ (batchCount + 1) * limbCap := by
  have hglobal' : LimbGlobalBound limbs (batchCount * limbCap) := hglobal
  have hsuffix' : LimbFutureBound iter limbs (batchCount * limbCap) := by
    intro i _
    exact hglobal i
  have hloop' : LimbLoop ops iter limbs sums = .ok out := by
    unfold LimbLoop
    exact hloop
  have hbound := limb_loop_success_batch_bound ops sums iter limbs out batchCount
    hsums hglobal' hsuffix' hloop'
  change ∀ i : Fin 8, cell out i ≤ (batchCount + 1) * limbCap at hbound
  exact hbound

#print axioms limb_loop_generated_call_batch_bound

end AspisR1FastDotsActualLimbFoldBodyFacadeV2
