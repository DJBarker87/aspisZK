import FourDotsActualTermExactRootV1
import FourDotsActualTermLoopLinearBoundV1
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualTermTraceRootV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev cap := AspisR1FastDotsActualInnerLoopLinearBoundV1.cap
abbrev cell := AspisR1FastDotsActualLimbLoopExactRootV1.cell
abbrev TermBody := AspisR1FastDotsActualTermBodyLinearBoundV1.TermBody
abbrev TermLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private def termStep (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    (Range × Array U64 8#usize) → Result (ControlFlow (Range × Array U64 8#usize)
      (Array U64 8#usize)) :=
  fun st => TermBody ops a a1 slot st.1 st.2

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

private theorem term_body_cont_progress (ops : Ops)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sumsFinal, _, hrest⟩ := bind_success _ _ _ hrest
      have hpair : (iter1, sumsFinal) = (iter', sums') :=
        ControlFlow.cont.inj (Result.ok.inj hrest)
      have hiter : iter1 = iter' := congrArg Prod.fst hpair
      have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
        intro x
        rfl
      have hltSpec : ∀ x y : Usize,
          core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
        intros
        rfl
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨_, hadvance⟩, hend⟩
        subst iter'
        exact ⟨hlt, hadvance, hend⟩
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _⟩
        cases hnone

private theorem term_body_done_identity (ops : Ops)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.done out)) : out = sums := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, _, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      change Result.ok (ControlFlow.done sums) = Result.ok (ControlFlow.done out) at hrest
      exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

structure Contribution where
  term : Usize
  bytes : Array U8 4#usize
  scalar : AspisR1FastDotsCurrent.aspis_core.field.M31
  wide : Wide
  coeff : Array Std.U32 8#usize

def Contribution.product (c : Contribution) (j : Fin 8) : Nat :=
  AspisR1FastDotsActualLimbLoopExactRootV1.coeffCell c.coeff j * c.scalar.val

def Contribution.matches (c : Contribution) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) (iter iter' : Range) : Prop :=
  core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some c.term,iter') ∧
  AspisR1FastDotsActualTermInputTraceRootV1.TermBytesTrace a slot c.term c.bytes ∧
  AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes c.bytes = .ok (some c.scalar) ∧
  c.scalar.val < 2147483647 ∧
  Array.index_usize a1 c.term = .ok c.wide ∧
  AspisR1EbyKPushWideToQ.toLimbs c.wide = .ok c.coeff

/-- A retained trace of the same source term bodies, with the exact products
from their parsed bytes and coefficient reads. -/
inductive ActualTermTrace (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    Range → Array U64 8#usize → Array U64 8#usize → List Contribution → Prop where
  | done (iter : Range) (sums : Array U64 8#usize)
      (hbody : TermBody ops a a1 slot iter sums = .ok (.done sums)) :
      ActualTermTrace ops a a1 slot iter sums sums []
  | step {iter iter' : Range} {sums sums' out : Array U64 8#usize}
      (c : Contribution) (tail : List Contribution)
      (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter',sums')))
      (hmatch : c.matches a a1 slot iter iter')
      (hvalue : ∀ j : Fin 8, cell sums' j = cell sums j + c.product j)
      (htail : ActualTermTrace ops a a1 slot iter' sums' out tail) :
      ActualTermTrace ops a a1 slot iter sums out (c::tail)

/-- Every retained source trace has the exact sum of its own contributions. -/
theorem actual_trace_exact_sum
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize) (cs : List Contribution)
    (htrace : ActualTermTrace ops a a1 slot iter sums out cs) :
    ∀ j : Fin 8, cell out j = cell sums j + (cs.map (fun c => c.product j)).sum := by
  induction htrace with
  | done iter sums hbody => intro j; simp only [List.map_nil,List.sum_nil,Nat.add_zero]
  | step c tail hbody hmatch hvalue htail ih =>
      intro j
      rw [ih j,hvalue j]
      simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

/-- A successful actual bounded term-range call supplies its own retained
input/product trace. All cell equations follow from source execution. -/
theorem actual_term_loop_success_trace
    (ops : Ops) (k : Nat) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) (iter : Range)
    (sums out : Array U64 8#usize) (d : Nat)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hsize : iter.end.val - iter.start.val ≤ d)
    (hbudget : k + d ≤ 4)
    (hloop : TermLoop (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        iter a a1 slot sums = .ok out) :
    ∃ cs : List Contribution,
      ActualTermTrace (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        a a1 slot iter sums out cs ∧
      cs.length ≤ d ∧
      ∀ j : Fin 8, cell out j = cell sums j + (cs.map (fun c => c.product j)).sum := by
  have htrace : ∃ cs : List Contribution,
      ActualTermTrace (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        a a1 slot iter sums out cs ∧ cs.length ≤ d := by
    induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
        generalizing iter sums k d with
    | h m ih =>
        change Aeneas.Std.loop (termStep
          (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops) a a1 slot)
          (iter,sums) = .ok out at hloop
        rcases loop_success_cases _ _ _ hloop with hdone | ⟨st',hcont,htail⟩
        · have hb : TermBody
              (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
              a a1 slot iter sums = .ok (.done out) := by
            simpa only [termStep] using hdone
          have hout := term_body_done_identity _ _ _ _ _ _ _ hb
          subst out
          exact ⟨[],.done iter sums hb,by simp only [List.length_nil]; omega⟩
        · rcases st' with ⟨iter',sums'⟩
          have hb : TermBody
              (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
              a a1 slot iter sums = .ok (.cont (iter',sums')) := by
            simpa only [termStep] using hcont
          obtain ⟨hlt,hadvance,hend⟩ := term_body_cont_progress _ a a1 slot iter iter' sums sums' hb
          have hdist : iter'.end.val - iter'.start.val + 1 = iter.end.val - iter.start.val := by
            rw [hend,hadvance]; omega
          have hdist' : iter'.end.val - iter'.start.val = iter.end.val - iter.start.val - 1 := by omega
          have hk3 : k ≤ 3 := by omega
          have hbase : ∀ j : Fin 8, cell sums j ≤ 3 * AspisR1FastDotsActualLimbLoopExactRootV1.cap := by
            intro j
            exact le_trans (hinput j) (Nat.mul_le_mul_right cap hk3)
          obtain ⟨term,bytes,scalar,wide,coeff,hnext,hbytes,hparse,hscalar,hread,hcoeff,hvalue⟩ :=
            AspisR1FastDotsActualTermExactRootV1.current_term_body_success_exact
              ops a a1 slot iter iter' sums sums' hcoord hbase hb
          have hsum' : ∀ i : Fin 8, cell sums' i ≤ (k+1)*cap :=
            AspisR1FastDotsActualTermBodyLinearBoundV1.current_term_body_success_linear_bound
              ops k hk3 a a1 slot iter iter' sums sums' hcoord hinput hb
          have hsize' : iter'.end.val - iter'.start.val ≤ d-1 := by omega
          have hbudget' : (k+1)+(d-1) ≤ 4 := by omega
          obtain ⟨cs,ht,hcs⟩ := ih (iter.end.val - iter.start.val - 1) (by omega)
            (k+1) iter' sums' (d-1) hsum' hsize' hbudget' htail hdist'
          let c : Contribution := ⟨term,bytes,scalar,wide,coeff⟩
          have hc : c.matches a a1 slot iter iter' :=
            ⟨hnext,hbytes,hparse,hscalar,hread,hcoeff⟩
          have hv : ∀ j : Fin 8, cell sums' j = cell sums j + c.product j := hvalue
          exact ⟨c::cs,.step c cs hb hc hv ht,by simp only [List.length_cons]; omega⟩
  obtain ⟨cs,ht,hlen⟩ := htrace
  exact ⟨cs,ht,hlen,actual_trace_exact_sum _ _ _ _ _ _ _ _ ht⟩

#print axioms actual_trace_exact_sum
#print axioms actual_term_loop_success_trace
end AspisR1FastDotsActualTermTraceRootV1
