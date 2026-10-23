import S9ActualPairWideOutputCanonicalV1
import S9ActualPairMixedHelperTransportV1
import S9ActualPairWideAddHelperTransportV1
import S9CandidateFoldMapPrimitivesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairScalarCallbackV1
local instance helperOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
abbrev Canonical := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev toHelperW := AspisR1S9ActualPairWideHelperTransportV1.toHelperW
abbrev toHelperQ := AspisR1S9ActualPairQMHelperTransportV1.toHelperQ
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev SC := weights.Weights.scalar_factor.closure
abbrev HC := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure

def mapClosure (c : SC) : HC := (mapArray toHelperW c.1,mapArray toHelperQ c.2)
def GoodArray (a : Array W 4#usize) : Prop :=
  ∀ (i : Usize) (v : W), Array.index_usize a i = .ok v → Canonical v

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- Same-run source callback refinement. All reads and arithmetic successes
are extracted from the accepted actual callback; the returned capture is
unchanged and the actual running accumulator remains canonical. -/
theorem actual_callback_success_maps (c cout : SC) (acc out : W) (i : Usize)
    (hp : GoodArray c.1) (hacc : Canonical acc)
    (h : weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      c (acc,i) = .ok (out,cout)) :
    cout = c ∧ Canonical out ∧
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        (mapClosure c) (toHelperW acc,i) = .ok (toHelperW out,mapClosure cout) := by
  unfold weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut at h
  obtain ⟨j,hj,h⟩ := bind_success _ _ _ h
  obtain ⟨p,hpRead,h⟩ := bind_success _ _ _ h
  obtain ⟨q,hqRead,h⟩ := bind_success _ _ _ h
  obtain ⟨term,hterm,h⟩ := bind_success _ _ _ h
  obtain ⟨total,htotal,h⟩ := bind_success _ _ _ h
  have heq : (total,c) = (out,cout) := Result.ok.inj h
  have ho : total = out := congrArg Prod.fst heq
  have hc : c = cout := congrArg Prod.snd heq
  subst out
  subst cout
  have hpcan : Canonical p := hp j p hpRead
  have htcan := AspisR1S9ActualPairWideOutputCanonicalV1.mul_qm31_success_canonical p term q hpcan hterm
  have hocan := AspisR1S9ActualPairWideOutputCanonicalV1.add_success_canonical acc term total hacc htcan htotal
  have hm := AspisR1S9ActualPairMixedHelperTransportV1.actual_pair_wide_mul_qm31_to_installed_helper p q hpcan
  rw [hterm] at hm
  have hmTarget : AspisR1S9HelperP6.field.WideExact.mul_qm31 (toHelperW p) (toHelperQ q) =
      .ok (toHelperW term) := hm.symm
  have ha := AspisR1S9ActualPairWideAddHelperTransportV1.actual_pair_wide_add_to_installed_helper acc term hacc htcan
  rw [htotal] at ha
  have haTarget : AspisR1S9HelperP6.field.WideExact.add (toHelperW acc) (toHelperW term) =
      .ok (toHelperW total) := ha.symm
  have hperm : weights.PERM = AspisR1S9HelperP6.weights.PERM := by
    unfold weights.PERM AspisR1S9HelperP6.weights.PERM
    rfl
  have hjTarget : Array.index_usize AspisR1S9HelperP6.weights.PERM i = .ok j := by
    rw [←hperm]
    exact hj
  have hpTarget : Array.index_usize (mapArray toHelperW c.1) j = .ok (toHelperW p) := by
    have hh := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toHelperW c.1 j
    rw [hpRead] at hh
    exact hh.symm
  have hqTarget : Array.index_usize (mapArray toHelperQ c.2) i = .ok (toHelperQ q) := by
    have hh := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toHelperQ c.2 i
    rw [hqRead] at hh
    exact hh.symm
  refine ⟨rfl,hocan,?_⟩
  unfold AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
  change (do
    let j ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
    let p ← Array.index_usize (mapArray toHelperW c.1) j
    let q ← Array.index_usize (mapArray toHelperQ c.2) i
    let term ← AspisR1S9HelperP6.field.WideExact.mul_qm31 p q
    let total ← AspisR1S9HelperP6.field.WideExact.add (toHelperW acc) term
    ok (total,mapClosure c)) = .ok (toHelperW total,mapClosure c)
  simp only [hjTarget,hpTarget,hqTarget,hmTarget,haTarget,bind_tc_ok]

#print axioms actual_callback_success_maps
end AspisR1S9ActualPairScalarCallbackV1
