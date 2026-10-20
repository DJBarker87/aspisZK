import CuSavingsRetainedResumeWeights
import AspisR1RhoTransactions.FunsExternal
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFinishRelation
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRetainedResumeOrigins CuSavingsRetainedResumeBinding
open CuSavingsRetainedCompositionWeightsInputs CuSavingsLibraConcrete CuSavingsLibraOrigins
attribute [local instance] CuSavingsLibraConcrete.shared
abbrev Factors := Array (Array (Array AspisR1S2Groups.field.QM31 4#usize) 5#usize) 5#usize
abbrev Points := Array (Array AspisR1S2Groups.field.QM31 10#usize) 3#usize
/-- Computational source fragments only. The constructor storage projection
excludes the fixed variant/extra field writes, which are retained below.
PointPrefix is the actual unchanged scratch/parts/point-row source frame;
PairTail is the exact parts4 update and kappa sum; FinalTail is the pair/claim
comparison, relation mark, final field-stream dot/check and final mark. -/
structure Boundaries (State : Type) where
  claimPrefix : AspisR1RhoTransactions.verifier.View → verifier.Prepared → Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  storage : verifier.Prepared → Result (core.result.Result (Factors × Points) verifier.Error)
  pairGuard : AspisR1S2Groups.Weights → verifier.Prepared → Slice U8 → Result (core.result.Result Unit verifier.Error)
  pointPrefix : AspisR1S2Groups.Weights → verifier.Prepared → Slice U8 → Parts → Parts → Result (core.result.Result State verifier.Error)
  pairTail : State → Low → GroupE → Parts → Result aspis_core.field.WideExact
  finalTail : AspisR1RhoTransactions.verifier.View → verifier.Prepared → verifier.Accumulator →
    Option (AspisR1RhoTransactions.verifier.Phase → Result Unit) → aspis_core.field.WideExact → aspis_core.field.WideExact → Result (core.result.Result Unit verifier.Error)
  fallback : AspisR1RhoTransactions.verifier.View → verifier.Prepared → verifier.Accumulator →
    Option (AspisR1RhoTransactions.verifier.Phase → Result Unit) → Result (core.result.Result Unit verifier.Error)

def groupK (q : AspisR1Libra.field.QM31) : AspisR1S2Groups.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def groupExtra (q : Extra) : Array AspisR1S2Groups.field.QM31 2#usize := arrayMap groupK q

variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]

def pairNew {State : Type} (B : Boundaries State) (p : verifier.Prepared)
    (bytes : Slice U8) (w : AspisR1S2Groups.Weights) (extra : Extra) : Result (core.result.Result aspis_core.field.WideExact verifier.Error) := do
  let a0 ← Array.index_usize p.alpha 0#usize
  let a1 ← Array.index_usize p.alpha 1#usize
  let ap0 ← CuSavingsLibraCaller.powersCaller (libra a0)
  let ap1 ← CuSavingsLibraCaller.powersCaller (libra a1)
  let state ← B.pointPrefix w p bytes ap0 ap1
  match state with
  | .Err error => .ok (.Err error)
  | .Ok state =>
    let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
    let inactive ← AspisR1S2Groups.new.grouped_inactive_pair w bytes (CuSavingsRetainedCompositionWeights.lowToGroup low)
    let parts ← AspisR1Libra.new.factored_s2_libra_weights ap0 ap1 extra
    let pair ← B.pairTail state low inactive parts
    .ok (.Ok pair)

def pairOld {State : Type} (B : Boundaries State) (p : verifier.Prepared)
    (bytes : Slice U8) (w : AspisR1S2Groups.Weights) (extra : Extra) : Result (core.result.Result aspis_core.field.WideExact verifier.Error) := do
  let a0 ← Array.index_usize p.alpha 0#usize
  let a1 ← Array.index_usize p.alpha 1#usize
  let ap0 ← CuSavingsLibraCaller.powersCaller (libra a0)
  let ap1 ← CuSavingsLibraCaller.powersCaller (libra a1)
  let state ← B.pointPrefix w p bytes ap0 ap1
  match state with
  | .Err error => .ok (.Err error)
  | .Ok state =>
    let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
    let inactive ← AspisR1S2Groups.old.grouped_inactive_pair w bytes (CuSavingsRetainedCompositionWeights.lowToGroup low)
    let parts ← AspisR1Libra.old.twofold_libra_weights low extra
    let pair ← B.pairTail state low inactive parts
    .ok (.Ok pair)

theorem pair_equivalence {State : Type} (B : Boundaries State) (p : verifier.Prepared)
    (bytes : Slice U8) (w : AspisR1S2Groups.Weights) (extra : Extra)
    (ha : ∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧ Alpha (libra a0) ∧ Alpha (libra a1))
    (he : ∀ i,i<2 → canonicalK (CuSavingsLibraSourceControl.lookup extra AspisR1Libra.field.QM31.ONE i)) :
    pairNew B p bytes w extra=pairOld B p bytes w extra := by
  obtain ⟨a0,a1,ha,ha0,ha1⟩ := ha
  have h0 : Array.index_usize p.alpha 0#usize=.ok a0 := by rw [ha];rfl
  have h1 : Array.index_usize p.alpha 1#usize=.ok a1 := by rw [ha];rfl
  obtain ⟨ap0,hp0,hv0⟩ := alpha_powers (libra a0) ha0
  obtain ⟨ap1,hp1,hv1⟩ := alpha_powers (libra a1) ha1
  simp only [pairNew,pairOld,h0,h1,hp0,hp1,bind_tc_ok]
  apply (bind_eq_iff (B.pointPrefix w p bytes ap0 ap1) _ _).mpr
  intro state hs
  cases state with
  | Err error => rfl
  | Ok state =>
    simp only [CuSavingsS2Candidate3.helper_equivalence]
    exact CuSavingsLibraCandidate14.caller_context ap0 ap1 extra
      (fun i hi => (hv0 i hi).1) (fun i hi => (hv1 i hi).1) he
      (fun low => AspisR1S2Groups.old.grouped_inactive_pair w bytes (CuSavingsRetainedCompositionWeights.lowToGroup low))
      (fun low inactive => do let out ← B.pairTail state low inactive; .ok (.Ok out))

#print axioms pair_equivalence
end AspisR1.CuSavingsRetainedFinishRelation
