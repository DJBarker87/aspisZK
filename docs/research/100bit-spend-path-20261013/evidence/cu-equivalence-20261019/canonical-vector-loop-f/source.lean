import CanonicalVectorSource
import CuSavingsCanonicalCandidate5
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalVectorLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
open OccupancyRangeTraversal
abbrev G := Array field.wide_exact.WideExact 29#usize
variable [Shared] [VectorCommon]

theorem old_step (g : G) (iter next : Range) (dot : old_pairing.EbyKDot)
    (value : field.wide_exact.WideExact)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,next))
    (hr : Array.index_usize g iter.start=.ok value) :
    old_callers.claim_dot_loop iter g dot = (do
      let scalar ← claim_scalar iter.start
      let (r,dot1) ← old_pairing.EbyKDot.push dot value scalar
      match r with
      | .Ok _ => old_callers.claim_dot_loop next g dot1
      | .Err _ => .ok (.Err Error.Parse)) := by
  unfold old_callers.claim_dot_loop
  rw [loop]
  dsimp only
  simp only [old_callers.claim_dot_loop.body,hn,bind_tc_ok,uncurry_apply_pair]
  cases hs : claim_scalar iter.start with
  | fail e => simp only [hs,bind_tc_fail]
  | div => simp only [hs,bind_tc_div]
  | ok scalar =>
    simp only [hs,bind_tc_ok]
    rw [hr]
    simp only [bind_tc_ok]
    cases hp : old_pairing.EbyKDot.push dot value scalar with
    | fail e => simp only [hp,bind_tc_fail]
    | div => simp only [hp,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨result,after⟩
      cases result <;>
        simp [hp,core.result.Result.map_err,
          old_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
          old_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem new_step (g : G) (iter next : Range) (dot : new_pairing.EbyKDot)
    (value : field.wide_exact.WideExact)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,next))
    (hr : Array.index_usize g iter.start=.ok value) :
    new_callers.claim_dot_loop iter g dot = (do
      let scalar ← claim_scalar iter.start
      let (r,dot1) ← new_pairing.EbyKDot.push dot value scalar
      match r with
      | .Ok _ => new_callers.claim_dot_loop next g dot1
      | .Err _ => .ok (.Err Error.Parse)) := by
  unfold new_callers.claim_dot_loop
  rw [loop]
  dsimp only
  simp only [new_callers.claim_dot_loop.body,hn,bind_tc_ok,uncurry_apply_pair]
  cases hs : claim_scalar iter.start with
  | fail e => simp only [hs,bind_tc_fail]
  | div => simp only [hs,bind_tc_div]
  | ok scalar =>
    simp only [hs,bind_tc_ok]
    rw [hr]
    simp only [bind_tc_ok]
    cases hp : new_pairing.EbyKDot.push dot value scalar with
    | fail e => simp only [hp,bind_tc_fail]
    | div => simp only [hp,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨result,after⟩
      cases result <;>
        simp [hp,core.result.Result.map_err,
          new_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
          new_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]


def CanonicalG (g : G) : Prop := ∀ i (hi:i<g.val.length),WideCanonical (g.val[i]'hi)

theorem g_read (g : G) (i : Usize) (hi:i.val<g.val.length) :
    Array.index_usize g i=.ok (g.val[i.val]'hi) := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]

theorem claim_loop (fuel : Nat) (g : G) (hg : CanonicalG g)
    (iter : Range) (dot : old_pairing.EbyKDot) (hcounts : RelatedCounts dot)
    (he : iter.end.val=29) (hi : iter.start.val≤29) (hf:29-iter.start.val=fuel) :
    new_callers.claim_dot_loop iter g (project dot)=old_callers.claim_dot_loop iter g dot := by
  induction fuel generalizing iter dot with
  | zero =>
      have hn := next_done iter (by omega)
      unfold new_callers.claim_dot_loop old_callers.claim_dot_loop
      rw [loop,loop]
      dsimp only
      simp only [new_callers.claim_dot_loop.body,old_callers.claim_dot_loop.body,
        hn,bind_tc_ok,uncurry_apply_pair]
      rw [CuSavingsCanonicalCandidate5.finalization]
      cases hfin : old_pairing.EbyKDot.finish dot <;>
        simp only [hfin,bind_tc_ok,bind_tc_fail,bind_tc_div]
  | succ fuel ih =>
      obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
      have hlen : g.val.length=29 := by simpa only [show (29#usize).val=29 by scalar_tac] using g.property
      have hb : iter.start.val<g.val.length := by omega
      let value := g.val[iter.start.val]'hb
      have hread := g_read g iter.start hb
      have hcan : WideCanonical value := hg iter.start.val hb
      rw [new_step g iter next (project dot) value hn hread,
        old_step g iter next dot value hn hread]
      apply (bind_eq_iff (claim_scalar iter.start) _ _).mpr
      intro scalar _
      rw [public_push dot value scalar hcan hcounts]
      simp only [bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]
      cases hp : old_pairing.EbyKDot.push dot value scalar with
      | fail error => rfl
      | div => rfl
      | ok pair =>
        rcases pair with ⟨result,after⟩
        cases result with
        | Err error => rfl
        | Ok unit =>
          have hnext := CuSavingsCanonicalDotsInvariant.push_counts dot after value scalar hcan hcounts hp
          exact ih next after hnext (by rw [hend];exact he) (by omega) (by omega)

theorem claim_source (g : G) (hg : CanonicalG g) :
    new_callers.claim_dot g=old_callers.claim_dot g := by
  simp only [new_callers.claim_dot,old_callers.claim_dot,
    CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new,bind_tc_ok]
  exact claim_loop 29 g hg {start:=0#usize,«end»:=29#usize}
    CuSavingsCanonicalDotsInvariant.initial CuSavingsCanonicalDotsInvariant.initial_counts
    (by scalar_tac) (by scalar_tac) (by scalar_tac)


def dotTable (values : Array CuSavingsCanonicalDotsSources.I 29#usize) : G :=
  ⟨values.val.map CuSavingsCanonicalDotsSources.inputToDot,
    by simpa only [List.length_map] using values.property⟩

theorem claim_from_powers [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
    (base : CuSavingsCanonicalDotsSources.I) (hb : CuSavingsCanonicalDotsSources.SourceValue base)
    (values : Array CuSavingsCanonicalDotsSources.I 29#usize)
    (h : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok values) :
    new_callers.claim_dot (dotTable values)=old_callers.claim_dot (dotTable values) := by
  apply claim_source
  intro i hi
  have hlen : values.val.length=(29#usize).val := values.property
  have hbnd : i<(29#usize).val := by simpa only [dotTable,List.length_map,hlen] using hi
  obtain ⟨out,hr,hc⟩ := CuSavingsCanonicalInputPowers.source_success 29#usize base
    (CuSavingsCanonicalDotsSources.source_canonical base hb)
  have heq := Result.ok.inj (hr.symm.trans h)
  cases heq
  change WideCanonical (CuSavingsCanonicalDotsSources.inputToDot (values.val[i]'_))
  exact CuSavingsCanonicalDotsSources.input_canonical _ (hc i hbnd).1

#print axioms new_step
#print axioms old_step
#print axioms g_read
#print axioms claim_loop
#print axioms claim_source
#print axioms claim_from_powers
end AspisR1.CuSavingsCanonicalVectorLoop
