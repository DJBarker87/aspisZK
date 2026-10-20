import CuSavingsRetainedResumeWhole
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeWeights
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRetainedResumeOrigins CuSavingsRetainedResumeBinding
open CuSavingsRetainedCompositionWeightsInputs CuSavingsLibraConcrete
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]
def scalar (q : aspis_core.field.QM31) : AspisR1RhoPowerTail.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem scalar_canonical (q : aspis_core.field.QM31) (hc : CuSavingsRhoInitRow.Canonical q) :
    canonicalK (libraK (scalar q)) := by
  exact ⟨⟨hc ⟨0,by decide⟩,hc ⟨1,by decide⟩⟩,⟨hc ⟨2,by decide⟩,hc ⟨3,by decide⟩⟩⟩

def pair {State Output : Type} (block : E → E → Extra → State → Result Output)
    (p : verifier.Prepared) (state : State) : Result Output := do
  let a0 ← Array.index_usize p.alpha 0#usize
  let a1 ← Array.index_usize p.alpha 1#usize
  let extra ← extraProjection (arrayMap scalar p.semantic_alpha)
  block (libra a0) (libra a1) extra state

theorem pair_equivalence {State Output : Type} (weights : State → AspisR1S2Groups.Weights)
    (bytes : Slice U8) (after : State → Low → GroupE → Parts → Result Output)
    (p : verifier.Prepared)
    (ha : ∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1))
    (hc : ∀ i hi,CuSavingsRhoInitRow.Canonical (p.semantic_alpha.val[i]'hi)) (state : State) :
    pair (blockNew weights bytes after) p state=pair (blockOld weights bytes after) p state := by
  obtain ⟨a0,a1,ha,ha0,ha1⟩ := ha
  have h0 : Array.index_usize p.alpha 0#usize=.ok a0 := by rw [ha];rfl
  have h1 : Array.index_usize p.alpha 1#usize=.ok a1 := by rw [ha];rfl
  have hs : ∀ i : Fin 10,canonicalK (libraK (semanticAt (arrayMap scalar p.semantic_alpha) i)) := by
    intro i
    unfold semanticAt arrayMap
    rw [List.getElem_map]
    exact scalar_canonical _ (hc i.val _)
  obtain ⟨extra,he,hcanon⟩ := extra_source_success (arrayMap scalar p.semantic_alpha) hs
  simp only [pair,h0,h1,he,bind_tc_ok]
  exact block_equivalence weights bytes after _ _ extra ha0 ha1 hcanon state

def sourceContext {State Output : Type} (B : Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (bytes proof publicValue : Slice U8) (v : transport.Variant) (hash : H)
    (block : verifier.Prepared → State → Result (core.result.Result Output verifier.Error))
    (context : verifier.Prepared → verifier.Accumulator →
      (State → Result (core.result.Result Output verifier.Error)) → Result (core.result.Result Output verifier.Error))
    (fallback : verifier.Prepared → verifier.Accumulator → Result (core.result.Result Output verifier.Error)) :
    Result (core.result.Result Output verifier.Error) :=
  letI : ResumeCommon := binding B
  do
  let restored ← source_resume_caller D bytes proof publicValue v hash
  match restored with
  | .Err error => .ok (.Err error)
  | .Ok (p,a) =>
    match v with
    | .S2 => context p a (block p)
    | _ => fallback p a

theorem source_context_equivalence {State Output : Type} (B : Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (bytes proof publicValue finalMessage : Slice U8)
    (v : transport.Variant) (hash : H)
    (weights : State → AspisR1S2Groups.Weights)
    (after : verifier.Prepared → State → Low → GroupE → Parts → Result (core.result.Result Output verifier.Error))
    (context : verifier.Prepared → verifier.Accumulator →
      (State → Result (core.result.Result Output verifier.Error)) → Result (core.result.Result Output verifier.Error))
    (fallback : verifier.Prepared → verifier.Accumulator → Result (core.result.Result Output verifier.Error)) :
    sourceContext B D bytes proof publicValue v hash
      (fun p => pair (blockNew weights finalMessage (after p)) p) context fallback =
    sourceContext B D bytes proof publicValue v hash
      (fun p => pair (blockOld weights finalMessage (after p)) p) context fallback := by
  letI : ResumeCommon := binding B
  unfold sourceContext
  apply (bind_eq_iff (source_resume_caller D bytes proof publicValue v hash) _ _).mpr
  intro restored hr
  cases restored with
  | Err error => rfl
  | Ok pair =>
    rcases pair with ⟨p,a⟩
    cases v with
    | S1 => rfl
    | D => rfl
    | S2 =>
      obtain ⟨_,ha,hc⟩ := CuSavingsRetainedResumeWhole.source_inputs B D bytes proof publicValue _ hash p a hr
      apply congrArg (context p a)
      funext state
      exact pair_equivalence weights finalMessage (after p) p ha hc state

#print axioms scalar_canonical
#print axioms pair_equivalence
#print axioms source_context_equivalence
end AspisR1.CuSavingsRetainedResumeWeights
