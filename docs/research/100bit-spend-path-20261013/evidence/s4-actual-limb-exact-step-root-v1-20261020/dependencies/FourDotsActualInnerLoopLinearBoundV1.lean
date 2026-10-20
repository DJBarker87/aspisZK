import FourDotsActualInnerLoopBoundV1
import FourDotsActualLimbLocalArithmeticV1
import FourDotsActualLimbPrefixStepV2
import Aeneas.Std.RangeIter
import Aeneas.Std.Array.Array
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualInnerLoopLinearBoundV1

abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Range := core.ops.range.Range Usize
abbrev InnerBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body
abbrev InnerLoop := AspisR1FastDotsActualInnerLoopBoundV1.InnerLoop
abbrev cap : Nat := (2147483646)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

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

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

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
          have hresult : result = out := Result.ok.inj h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp only [hs, bind_tc_ok] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private def innerStep (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) :
    (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31) →
      Result (ControlFlow (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31)
        (Array U64 8#usize)) :=
  fun s => InnerBody ops coeff s.1 s.2.1 s.2.2

private theorem body_success_starts_before_end
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    iter.start.val < iter.end.val := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some limb =>
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · exact hlt
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _⟩
        cases hnone

private theorem body_done_eq_sums
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter : Range)
    (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.done out)) : out = sums := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      change (Result.ok (ControlFlow.done sums) = Result.ok (ControlFlow.done out)) at hrest
      exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private theorem body_cont_scalar_eq
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    scalar' = scalar := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨updated, _, hrest⟩ := bind_success _ _ _ hrest
      have hpair : (iter1, updated, scalar) = (iter', sums', scalar') :=
        ControlFlow.cont.inj (Result.ok.inj hrest)
      exact (congrArg (fun p => p.2.2) hpair).symm

/-- A successful actual limb-loop step increases the uniform cap by at most
    one, while all later, as-yet-unvisited limbs retain the old cap. -/
theorem inner_body_success_linear_step
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (k : Nat) (hk : k ≤ 3)
    (coefficient : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hcoeff : ∀ i : Fin 8,
      (coefficient.val[i.val]'(by simpa [coefficient.property] using i.isLt)).val < 2147483647)
    (hbase : ∀ i : Fin 8, cell sums i ≤ (k + 1) * cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val → cell sums i ≤ k * cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : InnerBody ops coefficient iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
      (∀ i : Fin 8, iter'.start.val ≤ i.val → cell sums' i ≤ k * cap) ∧
      (∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap) := by
  have hcurrent : ∀ i : Fin 8, i.val = iter.start.val → cell sums i ≤ 3 * cap := by
    intro i hi
    have hge : iter.start.val ≤ i.val := by omega
    have hs := hsuffix i hge
    have hkcap : k * cap ≤ 3 * cap := Nat.mul_le_mul_right cap hk
    exact le_trans hs hkcap
  obtain ⟨limb, coeff, oldSum, product, newSum,
      hcoeffRead, hsumRead, hmul, hadd, hproductValue, hproductBound,
      hnewValue, updated, hupdate, hresult, hlimbEq, hOldBound,
      hiterStart, hiterEnd⟩ :=
    AspisR1FastDotsActualLimbLocalArithmeticV1.inner_body_success_arithmetic_at_current
      ops coefficient iter iter' sums sums' scalar scalar' hcoeff hcurrent hscalar hbody
  have hindex : limb.val < 8 := by
    have hi := index_success_bound sums limb oldSum hsumRead
    simpa [sums.property] using hi
  have holdK : oldSum.val ≤ k * cap := by
    let j : Fin 8 := ⟨limb.val, by simpa using hindex⟩
    have hlimbStart : j.val = iter.start.val := by
      change limb.val = iter.start.val
      exact congrArg UScalar.val hlimbEq
    have hget : oldSum = sums.val[limb.val]'(by simpa [sums.property] using hindex) := by
      have hidx : limb.val < sums.length := by simpa [sums.property] using hindex
      obtain ⟨x, hspec, hx⟩ := WP.spec_imp_exists (Array.index_usize_spec sums limb hidx)
      have hox : oldSum = x := Result.ok.inj (hsumRead.symm.trans hspec)
      exact hox.trans hx
    have hge : iter.start.val ≤ j.val := by omega
    have hs := hsuffix j hge
    have hgetJ : oldSum = sums.val[j.val]'(by simpa [sums.property] using j.isLt) := by
      simpa [j] using hget
    rw [hgetJ]
    exact hs
  have hnewBound : newSum.val ≤ (k + 1) * cap := by
    rw [hnewValue]
    calc
      oldSum.val + product.val ≤ k * cap + cap := Nat.add_le_add holdK hproductBound
      _ = (k + 1) * cap := by simp [Nat.add_mul]
  have hupdateSet : Array.update sums limb newSum = .ok (sums.set limb newSum) := by
    obtain ⟨out, hrun, hset⟩ := WP.spec_imp_exists
      (Array.update_spec sums limb newSum (by simpa [sums.property] using hindex))
    simpa only [hset] using hrun
  have hupdated : updated = sums.set limb newSum :=
    Result.ok.inj (hupdate.symm.trans hupdateSet)
  have hfinal : sums' = sums.set limb newSum := hresult.trans hupdated
  have hboundSet := AspisR1FastDotsActualLimbPrefixStepV2.set_preserves_pointwise_bound
    sums limb newSum ((k + 1) * cap) hbase hnewBound
  have hglobal : ∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap := by
    intro i
    rw [hfinal]
    exact hboundSet i
  refine ⟨hiterStart, hiterEnd, ?_, hglobal⟩
  intro i hi
  have hafter : iter.start.val < i.val := by rw [hiterStart] at hi; omega
  have hlimbNe : limb.val ≠ i.val := by rw [hlimbEq]; omega
  have hsetLength : i.val < (sums.val.set limb.val newSum).length := by
    simpa [sums.property] using i.isLt
  have horigLength : i.val < sums.val.length := by
    simpa [sums.property] using i.isLt
  have hsame : cell sums' i = cell sums i := by
    unfold cell
    rw [hfinal]
    change ((sums.val.set limb.val newSum)[i.val]'hsetLength).val =
      (sums.val[i.val]'horigLength).val
    rw [List.getElem_set_ne (l := sums.val) (i := limb.val) (j := i.val) hlimbNe hsetLength]
  rw [hsame]
  exact hsuffix i (by omega)

/-- The emitted eight-limb loop applies one bounded product to each visited
    limb. Given a k-cap bound at entry and canonical coefficient/scalar inputs,
    any successful loop result is bounded by (k+1)cap. -/
theorem inner_loop_success_linear_bound
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (k : Nat) (hk : k ≤ 3)
    (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (coefficient : Array U32 8#usize)
    (hcoeff : ∀ i : Fin 8,
      (coefficient.val[i.val]'(by simpa [coefficient.property] using i.isLt)).val < 2147483647)
    (hbase : ∀ i : Fin 8, cell sums i ≤ (k + 1) * cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val → cell sums i ≤ k * cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : InnerLoop ops iter sums scalar coefficient = .ok out) :
    ∀ i : Fin 8, cell out i ≤ (k + 1) * cap := by
  induction hmeasure : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums scalar with
  | h m ih =>
      change Aeneas.Std.loop (innerStep ops coefficient) (iter, sums, scalar) = .ok out at hloop
      rcases loop_success_cases (innerStep ops coefficient) (iter, sums, scalar) out hloop with
        hdone | ⟨state', hcont, htail⟩
      · have hbody : InnerBody ops coefficient iter sums scalar = .ok (.done out) := by
          simpa [innerStep] using hdone
        have hout := body_done_eq_sums ops coefficient iter sums out scalar hbody
        subst out
        exact hbase
      · rcases state' with ⟨iter', sums', scalar'⟩
        have hbody : InnerBody ops coefficient iter sums scalar =
            .ok (.cont (iter', sums', scalar')) := by
          simpa [innerStep] using hcont
        obtain ⟨hstart, hend, hsuffix', hbase''⟩ :=
          inner_body_success_linear_step ops k hk coefficient iter iter' sums sums'
            scalar scalar' hcoeff hbase hsuffix hscalar hbody
        have hscalarEq := body_cont_scalar_eq ops coefficient iter iter' sums sums' scalar scalar' hbody
        have hscalar' : scalar'.val < 2147483647 := by rw [hscalarEq]; exact hscalar
        have hlt := body_success_starts_before_end
          ops coefficient iter iter' sums sums' scalar scalar' hbody
        have hdecrease : iter.end.val - iter'.start.val < m := by
          rw [hstart]
          omega
        have htail' : InnerLoop ops iter' sums' scalar' coefficient = .ok out := by
          change Aeneas.Std.loop (innerStep ops coefficient) (iter', sums', scalar') = .ok out
          exact htail
        have hmeasure' : iter'.end.val - iter'.start.val = iter.end.val - iter'.start.val := by
          rw [hend]
        have htailBound := ih _ hdecrease iter' sums' scalar' hbase'' hsuffix' hscalar' htail' hmeasure'
        exact htailBound

#print axioms inner_body_success_linear_step
#print axioms inner_loop_success_linear_bound

end AspisR1FastDotsActualInnerLoopLinearBoundV1
