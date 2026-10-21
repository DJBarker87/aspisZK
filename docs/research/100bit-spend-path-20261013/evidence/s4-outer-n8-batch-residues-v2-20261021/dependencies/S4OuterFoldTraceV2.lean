import FourDotsActualBatchExactRootV1
import FourDotsActualBatchTermsAndLimbCallsV2
import FourDotsActualTermTraceRootV1
import FourDotsActualTermTraceBoundsRootV1
import FastDotFoldedBatches
import FourDotsActualSevenBatchLimbBoundV2
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsOuterFoldTraceV2
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev Body := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev BatchOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.BatchOps
abbrev Outer := AspisR1FastDotsActualSevenBatchLimbBoundV2.Outer
abbrev Cell := AspisR1FastDotsActualSevenBatchLimbBoundV2.cell
abbrev Contribution := AspisR1FastDotsActualTermTraceRootV1.Contribution
abbrev ActualOps := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
abbrev LimbOps := AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8

def batchDelta (cs : List Contribution) (j : Fin 8) : Nat :=
  AspisR1BatchedFoldSourceStep.fold ((cs.map fun c => c.product j).sum)

def rawBatchLists (ds : List (List Contribution)) (j : Fin 8) : List (List Nat) :=
  ds.map (fun cs => cs.map (fun c => c.product j))

private theorem trace_folded_sum (ds : List (List Contribution)) (j : Fin 8) :
    (ds.map fun cs => batchDelta cs j).sum =
      AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j) := by
  induction ds with
  | nil => rfl
  | cons cs rest ih =>
      change batchDelta cs j + (rest.map fun xs => batchDelta xs j).sum =
        AspisR1BatchedFoldArithmetic.fold
            ((cs.map fun c => c.product j).sum) +
          AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists rest j)
      rw [ih]
      rfl

/-- Full witness returned by the successful same-body batch theorem. Keeping
    it in the outer trace retains the parsed source trace and product bounds. -/
structure BatchWitness (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize)
    (it it' : StepBy) (limbs limbs' : Array U64 8#usize)
    (cs : List Contribution) where
  start : Usize
  batchEndArg : Usize
  rangeEnd : Usize
  sums : Array U64 8#usize
  next : core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it =
        .ok (some start,it')
  add4 : UScalar.add start 4#usize = .ok batchEndArg
  min26 : core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd
  terms : AspisR1FastDotsActualBatchTermsAndLimbCallsV2.TermLoop (ActualOps ops) {start, «end» := rangeEnd} a a1 slot
      (Array.repeat 8#usize 0#u64) = .ok sums
  sourceTrace : AspisR1FastDotsActualTermTraceRootV1.ActualTermTrace
      (ActualOps ops) a a1 slot {start, «end» := rangeEnd}
      (Array.repeat 8#usize 0#u64) sums cs
  length_le_four : cs.length ≤ 4
  products_le_cap : ∀ c ∈ cs, ∀ j : Fin 8, c.product j ≤ AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap
  delta : ∀ j : Fin 8, Cell limbs' j = Cell limbs j + batchDelta cs j

inductive ExactTrace (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    StepBy → Array U64 8#usize → Array U64 8#usize →
      List (List Contribution) → List Nat → Prop where
  | stop (it : StepBy) (limbs out : Array U64 8#usize)
      (hstep4 : it.step_by = 4#usize)
      (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.done out))
      (hout : out = limbs) : ExactTrace ops a a1 slot it limbs out [] []
  | step {it it' : StepBy} {limbs limbs' out : Array U64 8#usize}
      {cs : List Contribution} {tail : List (List Contribution)} {starts : List Nat}
      (hstep4 : it.step_by = 4#usize) (hnextStep4 : it'.step_by = 4#usize)
      (hstart : it.iter.start.val < it.iter.end.val)
      (hcursor : it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val)
      (hend : it'.iter.end = it.iter.end)
      (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.cont (it',limbs')))
      (hbatch : BatchWitness ops a a1 slot it it' limbs limbs' cs)
      (htail : ExactTrace ops a a1 slot it' limbs' out tail starts) :
      ExactTrace ops a a1 slot it limbs out (cs :: tail) (it.iter.start.val :: starts)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem outer_equation (ops : Ops) (it : StepBy) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) (limbs : Array U64 8#usize) :
    Outer (BatchOps (LimbOps ops)) it a a1 slot limbs =
      match Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
      | .ok (.cont (it',limbs')) => Outer (BatchOps (LimbOps ops)) it' a a1 slot limbs'
      | .ok (.done out) => .ok out
      | .fail e => .fail e
      | .div => .div := by
  change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
    (BatchOps (LimbOps ops)) it a a1 slot limbs = _
  conv_lhs => unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0; rw [loop]
  cases hb : Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow => cases flow with
    | done out => simp only [hb, bind_tc_ok]
    | cont pair => simp only [hb, bind_tc_ok]; cases pair with | mk it' limbs' => rfl

private theorem done_identity (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (it : StepBy) (limbs out : Array U64 8#usize)
    (hstep : it.step_by = 4#usize)
    (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.done out)) : out = limbs := by
  have _hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
    (BatchOps ops) a a1 slot it limbs out hstep hbody
  unfold Body at hbody
  obtain ⟨⟨o,it1⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      have hpositive : it.step_by.val > 0 := by rw [hstep]; simp
      have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it hpositive
      rw [hnext, WP.spec_ok] at hspec
      have hnot : ¬ it.iter.start.val < it.iter.end.val := by omega
      simp only [hnot,↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
      simp at hnone

private theorem outer_success_exact_trace
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (it : StepBy) (limbs out : Array U64 8#usize)
    (hend : it.iter.end.val = 26) (hstep : it.step_by = 4#usize)
    (hcoords : ∀ i : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer (BatchOps (LimbOps ops)) it a a1 slot limbs = .ok out) :
    ∃ ds starts, ExactTrace ops a a1 slot it limbs out ds starts := by
  induction hmeasure : it.iter.end.val - it.iter.start.val
      using Nat.strong_induction_on generalizing it limbs with
  | h m ih =>
      rw [outer_equation] at houter
      cases hb : Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
      | fail e => simp only [hb,bind_tc_fail] at houter; cases houter
      | div => simp only [hb,bind_tc_div] at houter; cases houter
      | ok flow =>
          cases flow with
          | done out0 =>
              simp only [hb,bind_tc_ok] at houter
              have heq : out0 = out := Result.ok.inj houter
              subst out
              have hid := done_identity ops a a1 slot it limbs out0 hstep hb
              exact ⟨[], [], .stop it limbs out0 hstep hb hid⟩
          | cont pair =>
              rcases pair with ⟨it',limbs'⟩
              simp only [hb,bind_tc_ok] at houter
              obtain ⟨_,hnext,_,hcursor,hend',hstep'⟩ :=
                AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
                  (BatchOps ops) a a1 slot it it' limbs limbs' hstep hb
              obtain ⟨start,batchEndArg,rangeEnd,sums,cs,hnextBatch,hadd,hmin,hterms,htrace,hlen,hproducts,hdelta⟩ :=
                AspisR1FastDotsActualBatchExactRootV1.current_batch_body_success_exact
                  (LimbOps ops) a a1 slot it it' limbs limbs' hend hcoords hstep hb
              have hpos : it.step_by.val > 0 := by rw [hstep]; simp
              have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it hpos
              rw [hnext,WP.spec_ok] at hspec
              have hlt : it.iter.start.val < it.iter.end.val := by
                by_contra hn
                simp only [hn,↓reduceIte] at hspec
                rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
                cases hnone
              have hdecrease : it'.iter.end.val - it'.iter.start.val < m := by
                rw [hend',hcursor]
                by_cases hm : it.iter.start.val + it.step_by.val ≤ it.iter.end.val
                · rw [Nat.min_eq_left hm]
                  rw [hstep] at hm
                  omega
                · have hm' : it.iter.end.val ≤ it.iter.start.val + it.step_by.val := by omega
                  rw [Nat.min_eq_right hm']
                  omega
              have hendTail : it'.iter.end.val = 26 := by rw [hend']; exact hend
              have hstepNext4 : it'.step_by = 4#usize := by rw [hstep']; exact hstep
              obtain ⟨ds,starts, htail⟩ := ih _ hdecrease it' limbs' hendTail hstepNext4 houter rfl
              let hbatch : BatchWitness ops a a1 slot it it' limbs limbs' cs := {
                start := start, batchEndArg := batchEndArg, rangeEnd := rangeEnd,
                sums := sums, next := hnextBatch, add4 := hadd, min26 := hmin,
                terms := hterms, sourceTrace := htrace, length_le_four := hlen,
                products_le_cap := hproducts, delta := hdelta }
              exact ⟨cs :: ds, it.iter.start.val :: starts,
                .step hstep hstepNext4 hlt hcursor hend' hb hbatch htail⟩

private theorem trace_cell_sum {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    ∀ j : Fin 8, Cell out j = Cell limbs j + (ds.map fun cs => batchDelta cs j).sum := by
  induction h with
  | stop it limbs out hstep4 hbody hout =>
      intro j
      simp [hout, Cell]
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart hcursor hend hbody hbatch htail ih =>
      intro j
      rw [ih j, hbatch.delta j]
      simp [batchDelta, Nat.add_assoc]

private theorem trace_batch_shape {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    AspisR1FastDotsBatchLoopSchedule.BatchTrace it starts := by
  induction h with
  | stop it limbs out hstep4 hbody hout =>
      have hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
        (BatchOps ops) a a1 slot it limbs out hstep4 hbody
      exact .stop it hstop
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart hcursor hend hbody hbatch htail ih =>
      exact .step hstart hcursor hend (hnextStep4.trans hstep4.symm) ih

private theorem trace_lengths {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    ds.length = starts.length := by
  induction h with
  | stop => rfl
  | step _ _ _ _ _ _ _ htail ih => simp [ih]

private theorem trace_batch_limits {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    ∀ cs ∈ ds, cs.length ≤ 4 ∧
      ∀ c ∈ cs, ∀ j : Fin 8,
        c.product j ≤ AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap := by
  induction h with
  | stop => simp
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart hcursor hend hbody hbatch htail ih =>
      intro xs hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨hbatch.length_le_four, hbatch.products_le_cap⟩
      · exact ih xs hmem

/-- The selected actual outer execution has an exact source-preserving fold
    equation for every limb. Its seven per-batch lists come from the same
    successful emitted bodies and accumulator calls. -/
theorem actual_outer_success_exact_fold_sum
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer (BatchOps (LimbOps ops)) AspisR1FastDotsStepSchedule.startBy a a1 slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∃ (ds : List (List Contribution)) (starts : List Nat),
      ExactTrace ops a a1 slot AspisR1FastDotsStepSchedule.startBy
        (Array.repeat 8#usize 0#u64) out ds starts ∧ ds.length = 7 ∧
      (∀ cs ∈ ds, cs.length ≤ 4 ∧
        ∀ c ∈ cs, ∀ j : Fin 8,
          c.product j ≤ AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap) ∧
      ∀ j : Fin 8, Cell out j = (ds.map fun cs => batchDelta cs j).sum := by
  obtain ⟨ds, starts, htrace⟩ := outer_success_exact_trace ops a a1 slot
    AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) out
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) hcoords houter
  have hbatch := trace_batch_shape htrace
  have hshape := AspisR1FastDotsBatchExactSeven.trace_shape_from 7 0
    AspisR1FastDotsStepSchedule.startBy starts rfl (by omega)
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) hbatch
  have hlen : starts.length = 7 := by rw [hshape]; rfl
  have hdslen := trace_lengths htrace
  have hlimits := trace_batch_limits htrace
  have hsum := trace_cell_sum htrace
  have hzero : ∀ j : Fin 8, Cell (Array.repeat 8#usize 0#u64) j = 0 := by
    intro j
    fin_cases j <;> rfl
  refine ⟨ds, starts, htrace, hdslen.trans hlen, hlimits, ?_⟩
  intro j
  simpa [hzero j] using hsum j

/-- The same seven lists retained by the outer trace satisfy the actual
    seven-batch reducer theorem. The returned source accumulator cell is thus
    reduced to the unreduced sum of its exact parsed products. -/
theorem actual_outer_success_reducer_residue
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer (BatchOps (LimbOps ops)) AspisR1FastDotsStepSchedule.startBy a a1 slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∃ (ds : List (List Contribution)) (starts : List Nat),
      ExactTrace ops a a1 slot AspisR1FastDotsStepSchedule.startBy
        (Array.repeat 8#usize 0#u64) out ds starts ∧ ds.length = 7 ∧
      (∀ cs ∈ ds, cs.length ≤ 4 ∧
        ∀ c ∈ cs, ∀ j : Fin 8,
          c.product j ≤ AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap) ∧
      ∀ j : Fin 8, ∃ z : AspisR1Qm31ArithmeticProbe.field.M31,
        AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
          (out.val[j.val]'(by simpa [out.property] using j.isLt)) = .ok z ∧
        z.val = AspisR1.FastDotFoldedBatches.fullSum (rawBatchLists ds j) %
          AspisR1BatchedFoldArithmetic.modulus ∧
        z.val < AspisR1BatchedFoldArithmetic.modulus := by
  obtain ⟨ds,starts,htrace,hlen,hlimits,hcells⟩ :=
    actual_outer_success_exact_fold_sum ops a a1 slot out hcoords houter
  refine ⟨ds,starts,htrace,hlen,hlimits,?_⟩
  intro j
  have hboundList : ∀ xs ∈ rawBatchLists ds j,
      xs.length ≤ 4 ∧ ∀ x ∈ xs, x ≤ AspisR1.FastDotFoldedBatches.cap := by
    intro xs hxs
    simp only [rawBatchLists,List.mem_map] at hxs
    rcases hxs with ⟨cs,hcs,hxs⟩
    subst xs
    obtain ⟨hlenCs,hprodCs⟩ := hlimits cs hcs
    constructor
    · simpa [rawBatchLists] using hlenCs
    · intro x hx
      simp only [List.mem_map] at hx
      rcases hx with ⟨c,hc,rfl⟩
      exact hprodCs c hc j
  have hcount : (rawBatchLists ds j).length ≤ 7 := by
    simp only [rawBatchLists,List.length_map]
    omega
  obtain ⟨z,hred,hvalue,hcanonical⟩ :=
    AspisR1.FastDotFoldedBatches.actual_reducer_after_seven
      (rawBatchLists ds j) hcount hboundList
  have hfolded : Cell out j =
      AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j) := by
    rw [hcells j, trace_folded_sum]
  let word : U64 := out.val[j.val]'(by simpa [out.property] using j.isLt)
  have hwordValue : word.val =
      AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j) := by
    change Cell out j = AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j)
    exact hfolded
  have hwordBound :
      AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j) < 2^64 :=
    (AspisR1.FastDotFoldedBatches.seven_batches_u64
      (rawBatchLists ds j) hcount hboundList).2
  have hword : word = (UScalar.ofNatCore
      (AspisR1.FastDotFoldedBatches.foldedSum (rawBatchLists ds j)) hwordBound : U64) := by
    apply UScalar.eq_of_val_eq
    exact hwordValue
  have hredWord :
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 word = .ok z := by
    rw [hword]
    exact hred
  refine ⟨z, ?_, hvalue, hcanonical⟩
  simpa [word] using hredWord

#print axioms actual_outer_success_exact_fold_sum
#print axioms actual_outer_success_reducer_residue
end AspisR1FastDotsOuterFoldTraceV2
