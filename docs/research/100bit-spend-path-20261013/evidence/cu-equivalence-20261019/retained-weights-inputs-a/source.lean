import CuSavingsRetainedCompositionWeights
import CuSavingsRetainedCompositionWeightsExtraSource
import CuSavingsRetainedPreparationInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionWeightsInputs
open Aeneas Aeneas.Std Result
open CuSavingsLibraConcrete CuSavingsLibraOrigins
attribute [local instance] CuSavingsLibraConcrete.shared
namespace P
abbrev K := AspisR1RhoPowerTail.aspis_core.field.QM31
abbrev E := AspisR1RhoPowerTail.aspis_core.field.WideExact
abbrev Prepared := AspisR1RhoPowerTail.verifier.Prepared
end P
abbrev E := AspisR1Libra.field.wide_exact.WideExact
abbrev Extra := Array AspisR1Libra.field.QM31 2#usize
abbrev Low := Array E 16#usize
abbrev Parts := Array E 4#usize
abbrev GroupE := CuSavingsRetainedCompositionWeights.GroupE

private theorem readAt {T : Type} {N : Usize} (xs : Array T N) (i : Usize)
    (hi : i.val < xs.val.length) : Array.index_usize xs i=.ok (xs.val[i.val]'hi) := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]

def alphaAt (p : P.Prepared) (i : Fin 2) : P.E :=
  p.alpha.val[i.val]'(by rw [p.alpha.property];simpa using i.isLt)
def semanticAt (xs : Array P.K 10#usize) (i : Fin 10) : P.K :=
  xs.val[i.val]'(by rw [xs.property];simpa using i.isLt)
def extraProjection (xs : Array P.K 10#usize) : Result Extra := do
  let raw ← AspisR1RhoPowerTail.retained.weights_extra xs
  .ok (CuSavingsRetainedSemanticBinding.array CuSavingsRetainedSemanticBinding.libraK raw)

theorem extra_source_success (xs : Array P.K 10#usize)
    (hc : ∀ i : Fin 10,canonicalK (CuSavingsRetainedSemanticBinding.libraK (semanticAt xs i))) :
    ∃ extra,extraProjection xs=.ok extra ∧
      ∀ i,i < 2 → canonicalK (CuSavingsLibraSourceControl.lookup extra AspisR1Libra.field.QM31.ONE i) := by
  let x := semanticAt xs ⟨8,by decide⟩
  let y := semanticAt xs ⟨9,by decide⟩
  have h8 : Array.index_usize xs 8#usize=.ok x := readAt xs _ (by rw [xs.property];scalar_tac)
  have h9 : Array.index_usize xs 9#usize=.ok y := readAt xs _ (by rw [xs.property];scalar_tac)
  let extra := Array.make 2#usize [CuSavingsRetainedSemanticBinding.libraK x,CuSavingsRetainedSemanticBinding.libraK y]
  refine ⟨extra,?_,?_⟩
  · unfold extraProjection AspisR1RhoPowerTail.retained.weights_extra
    rw [h8,h9]
    rfl
  · intro i hi
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with h|h
    · subst i
      exact hc ⟨8,by decide⟩
    · subst i
      exact hc ⟨9,by decide⟩

variable [AspisR1S2Groups.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]

def blockNew {State Output : Type} (weights : State → AspisR1S2Groups.Weights)
    (bytes : Slice U8) (after : State → Low → GroupE → Parts → Result Output)
    (a0 a1 : E) (extra : Extra) (state : State) : Result Output := do
  let ap0 ← CuSavingsLibraCaller.powersCaller a0
  let ap1 ← CuSavingsLibraCaller.powersCaller a1
  let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
  let inactive ← AspisR1S2Groups.new.grouped_inactive_pair (weights state) bytes
    (CuSavingsRetainedCompositionWeights.lowToGroup low)
  let libra ← AspisR1Libra.new.factored_s2_libra_weights ap0 ap1 extra
  after state low inactive libra

def blockOld {State Output : Type} (weights : State → AspisR1S2Groups.Weights)
    (bytes : Slice U8) (after : State → Low → GroupE → Parts → Result Output)
    (a0 a1 : E) (extra : Extra) (state : State) : Result Output := do
  let ap0 ← CuSavingsLibraCaller.powersCaller a0
  let ap1 ← CuSavingsLibraCaller.powersCaller a1
  let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
  let inactive ← AspisR1S2Groups.old.grouped_inactive_pair (weights state) bytes
    (CuSavingsRetainedCompositionWeights.lowToGroup low)
  let libra ← AspisR1Libra.old.twofold_libra_weights low extra
  after state low inactive libra

theorem block_equivalence {State Output : Type} (weights : State → AspisR1S2Groups.Weights)
    (bytes : Slice U8) (after : State → Low → GroupE → Parts → Result Output)
    (a0 a1 : E) (extra : Extra) (ha0 : Alpha a0) (ha1 : Alpha a1)
    (he : ∀ i,i < 2 → canonicalK (CuSavingsLibraSourceControl.lookup extra AspisR1Libra.field.QM31.ONE i))
    (state : State) : blockNew weights bytes after a0 a1 extra state=blockOld weights bytes after a0 a1 extra state := by
  obtain ⟨ap0,hp0,hv0⟩ := alpha_powers a0 ha0
  obtain ⟨ap1,hp1,hv1⟩ := alpha_powers a1 ha1
  simp only [blockNew,blockOld,hp0,hp1,bind_tc_ok,CuSavingsS2Candidate3.helper_equivalence]
  exact CuSavingsLibraCandidate14.caller_context ap0 ap1 extra
    (fun i hi => (hv0 i hi).1) (fun i hi => (hv1 i hi).1) he
    (fun low => AspisR1S2Groups.old.grouped_inactive_pair (weights state) bytes
      (CuSavingsRetainedCompositionWeights.lowToGroup low)) (after state)

def pair {State Output : Type}
    (block : E → E → Extra → State → Result Output) (p : P.Prepared) (state : State) : Result Output := do
  let a0 ← Array.index_usize p.alpha 0#usize
  let a1 ← Array.index_usize p.alpha 1#usize
  let extra ← extraProjection p.semantic_alpha
  block (CuSavingsRetainedSamplerBinding.libra a0) (CuSavingsRetainedSamplerBinding.libra a1) extra state

theorem pair_equivalence {State Output : Type} (weights : State → AspisR1S2Groups.Weights)
    (bytes : Slice U8) (after : State → Low → GroupE → Parts → Result Output)
    (p : P.Prepared)
    (ha : ∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧
      Alpha (CuSavingsRetainedSamplerBinding.libra a0) ∧ Alpha (CuSavingsRetainedSamplerBinding.libra a1))
    (hc : ∀ i : Fin 10,canonicalK (CuSavingsRetainedSemanticBinding.libraK (semanticAt p.semantic_alpha i)))
    (state : State) :
    pair (blockNew weights bytes after) p state=pair (blockOld weights bytes after) p state := by
  obtain ⟨a0,a1,ha,ha0,ha1⟩ := ha
  have h0 : Array.index_usize p.alpha 0#usize=.ok a0 := by rw [ha];rfl
  have h1 : Array.index_usize p.alpha 1#usize=.ok a1 := by rw [ha];rfl
  obtain ⟨extra,he,hcanon⟩ := extra_source_success p.semantic_alpha hc
  simp only [pair,h0,h1,he,bind_tc_ok]
  exact block_equivalence weights bytes after _ _ extra ha0 ha1 hcanon state

#print axioms extra_source_success
#print axioms block_equivalence
#print axioms pair_equivalence
end AspisR1.CuSavingsRetainedCompositionWeightsInputs
