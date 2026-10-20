import AspisR1RhoQuery.Funs
import CuSavingsRhoAccumulate
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoQuery
open Aeneas Aeneas.Std Result AspisR1RhoQuery
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoFinishModel
variable [AspisR1RhoAccumulate.AccumulateCommon] [QueryCommon]
abbrev Acc := verifier.Accumulator
abbrev Prep := verifier.Prepared
abbrev BW := BatchedWeights
def canonicalVec (b : BW) : alloc.vec.Vec aspis_core.field.QM31 := canonicalSlice b

/-- Actual old variant-dependent wrapper and new direct selection agree,
including node-computation failures. No domain-node property is assumed. -/
theorem node_equivalence (p : Prep) (geometry : QueryGeometry) (i u : Usize) :
    source_node_old p geometry i u = source_node_new p geometry i u := by
  cases hv : p.variant <;>
    simp [source_node_old,source_node_new,transport.Variant.folds,
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq,hv,
      read_discriminant,AspisR1RhoPowerTail.transport.Variant.read_discriminant] <;>
    cases source_line_node u <;> rfl

def observe (r : core.result.Result (Acc × BW) verifier.Error) :
    Result (core.result.Result Acc verifier.Error) := do
  match r with
  | .Err e => .ok (.Err e)
  | .Ok (a,b) =>
    let weights ← AspisR1CuRhoSource.verifier.BatchedWeights.finish b a.weights
    .ok (.Ok {a with weights:=weights})

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Common mark sees only the original query index. The actual materializer
can therefore be moved across it once source accumulation establishes its
successful handback and length. -/
theorem accumulation_context (p : Prep) (a : Acc) (b : BW) (node : U32)
    (value : aspis_core.field.WideExact)
    (hg : Good b []) (hp : Canonical a.power) (hr : Canonical p.rho)
    (hn : a.next.val < 22) (hc : b.terms.val < 22)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length)
    (obs : Option (verifier.Phase → Result Unit)) :
    (do let out ← factored_old.accumulate_with_node p {a with weights:=canonicalVec b} node value
        verifier.mark obs (.Query a.next)
        .ok (core.result.Result.Ok out)) =
    (do let (out,pending) ← factored_new.accumulate_with_node p a node value (some b)
        let b' := match pending with | some x => x | none => b
        verifier.mark obs (.Query a.next)
        observe (.Ok (out,b'))) := by
  have heq := CuSavingsRhoAccumulate.source_equivalence p a b node value hg hp (by omega) hc hl hrows
  change factored_old.accumulate_with_node p {a with weights:=canonicalVec b} node value = _ at heq
  simp only [factored_old.accumulate_with_node,factored_new.accumulate_with_node] at heq ⊢
  cases hm : AspisR1RhoAccumulate.factored_new.accumulate_with_node p a node value (some b) with
  | fail e =>
    simp only [hm,bind_tc_fail] at heq ⊢
    rw [heq]
    rfl
  | div =>
    simp only [hm,bind_tc_div] at heq ⊢
    rw [heq]
    rfl
  | ok result =>
    rcases result with ⟨result,pending⟩
    obtain ⟨out,hout,hgood,_,hlen,hw,_,_,_⟩ :=
      CuSavingsRhoAccumulate.source_preserves p a b node value hg hp hr hn hc hl hrows (result,pending) hm
    change pending=some out at hout
    subst pending
    have hf := CuSavingsRhoSourceFinish.source_success out result.weights
      (show result.weights.val.length=out.raw.val.length by rw [hw,hlen,hrows])
    simp only [hm,bind_tc_ok,CuSavingsRhoAccumulate.materialize,hf] at heq
    simp only [heq,hm,bind_tc_ok,uncurry_apply_pair,observe,hf]

/-- Whole query result including rejection and divergence; prefix is the same
actual hash/check computation with the same query index. -/
theorem source_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : Prep) (a : Acc) (b : BW)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (hg : Good b []) (hp : Canonical a.power) (hr : Canonical p.rho)
    (hn : a.next.val < 22) (hc : b.terms.val < 22)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length) :
    query_old.query_with_geometry digest v p {a with weights:=canonicalVec b} g hash obs geometry =
    (do let r ← query_new.query_with_geometry digest v p a g hash obs geometry b
        observe r) := by
  unfold query_old.query_with_geometry query_new.query_with_geometry
  simp only [bind_assoc_eq]
  simp only [node_equivalence]
  cases hpre : source_query_prefix digest v p g hash obs geometry a.next with
  | fail e => simp only [hpre,bind_tc_fail]
  | div => simp only [hpre,bind_tc_div]
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok val =>
      rcases val with ⟨u,folded⟩
      simp only [hpre,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,uncurry_apply_pair]
      cases hnode : source_node_new p geometry a.next u with
      | fail e => simp only [hnode,bind_tc_fail]
      | div => simp only [hnode,bind_tc_div]
      | ok node =>
        simp only [hnode,bind_tc_ok]
        rw [accumulation_context p a b node folded hg hp hr hn hc hl hrows obs]
        cases hm : factored_new.accumulate_with_node p a node folded (some b) with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨acc,pending⟩
          simp only [bind_tc_ok]
          cases verifier.mark obs (.Query a.next) <;> rfl

/-- Derive stage-loop arithmetic state from the successful whole query,
including the actual prefix/checks, selection, accumulation and mark. -/
theorem source_success {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : Prep) (a : Acc) (b : BW)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (hg : Good b []) (hp : Canonical a.power) (hr : Canonical p.rho)
    (hn : a.next.val < 22) (hc : b.terms.val < 22)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length) (result : Acc × BW)
    (h : query_new.query_with_geometry digest v p a g hash obs geometry b = .ok (.Ok result)) :
    Good result.2 [] ∧ result.2.terms.val=b.terms.val+1 ∧
      result.2.raw.val.length=b.raw.val.length ∧ result.1.weights=a.weights ∧
      Canonical result.1.power ∧ result.1.next.val=a.next.val+1 ∧ result.1.next.val ≤ 22 := by
  unfold query_new.query_with_geometry at h
  obtain ⟨r,_,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err e => cases h
  | Ok pair =>
    rcases pair with ⟨u,folded⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨node,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨out,hacc,h⟩ := bind_ok _ _ _ h
    rcases out with ⟨acc,pending⟩
    obtain ⟨bw,hbw,hgood,hcount,hlen,hw,hpower,hnext,hbound⟩ :=
      CuSavingsRhoAccumulate.source_preserves p a b node folded hg hp hr hn hc hl hrows (acc,pending) hacc
    change pending=some bw at hbw
    subst pending
    simp only [uncurry_apply_pair] at h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    have heq : (acc,bw)=result := core.result.Result.Ok.inj (Result.ok.inj h)
    cases heq
    exact ⟨hgood,hcount,hlen,hw,hpower,hnext,hbound⟩

#print axioms source_success
#print axioms node_equivalence
#print axioms accumulation_context
#print axioms source_equivalence
#print axioms observe
end AspisR1.CuSavingsRhoQuery
