import CuSavingsRhoStage
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoCryptographicTrace
open Aeneas Aeneas.Std Result AspisR1RhoQuery
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoFinishModel
variable [AspisR1RhoAccumulate.AccumulateCommon] [QueryCommon]

/- Source trace projection: every iteration first calls the identical prefix
with its current query index. All cryptographic calls within a query are in
that prefix; changed node/accumulation/materialization paths call no hashes.
Record the prefix even if its query subsequently rejects, fails or diverges. -/
def oldCalls {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (g : Array aspis_core.field.WideExact 29#usize)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (end1 : Usize) : Nat → verifier.Accumulator → List Usize
  | 0,_ => []
  | fuel+1,a =>
    if a.next < end1 then a.next ::
      (match query_old.query_with_geometry digest v p a g hash obs geometry with
       | .ok (.Ok out) => oldCalls digest v p g hash obs geometry end1 fuel out
       | _ => [])
    else []

def newCalls {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (g : Array aspis_core.field.WideExact 29#usize)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (end1 : Usize) : Nat → verifier.Accumulator → BatchedWeights → List Usize
  | 0,_,_ => []
  | fuel+1,a,b =>
    if a.next < end1 then a.next ::
      (match query_new.query_with_geometry digest v p a g hash obs geometry b with
       | .ok (.Ok (out,pending)) => newCalls digest v p g hash obs geometry end1 fuel out pending
       | _ => [])
    else []

/-- Equality of the source prefix-invocation schedule, including the failing
query. Inputs other than index are fixed and identical throughout the stage. -/
theorem calls_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (g : Array aspis_core.field.WideExact 29#usize)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (end1 : Usize) (he : end1.val ≤ 22) (hr : Canonical p.rho)
    (fuel : Nat) (a : verifier.Accumulator) (b : BatchedWeights)
    (hg : Good b []) (hp : Canonical a.power) (hc : b.terms.val ≤ a.next.val)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length) :
    oldCalls digest v p g hash obs geometry end1 fuel
      {a with weights:=CuSavingsRhoQuery.canonicalVec b} =
    newCalls digest v p g hash obs geometry end1 fuel a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
    by_cases hgo : a.next < end1
    · have hn : a.next.val < 22 := by change a.next.val < end1.val at hgo;omega
      have hcount : b.terms.val < 22 := by omega
      have heq := CuSavingsRhoQuery.source_equivalence digest v p a b g hash obs geometry hg hp hr hn hcount hl hrows
      simp only [oldCalls,newCalls,hgo,if_pos]
      cases hq : query_new.query_with_geometry digest v p a g hash obs geometry b with
      | fail e =>
        simp only [hq,bind_tc_fail] at heq
        simp only [heq]
      | div =>
        simp only [hq,bind_tc_div] at heq
        simp only [heq]
      | ok r =>
        cases r with
        | Err e =>
          simp only [hq,bind_tc_ok,CuSavingsRhoQuery.observe] at heq
          simp only [heq]
        | Ok pair =>
          rcases pair with ⟨a',b'⟩
          obtain ⟨hg',hcount',hlen',hw',hp',hnext',_⟩ :=
            CuSavingsRhoQuery.source_success digest v p a b g hash obs geometry hg hp hr hn hcount hl hrows (a',b') hq
          dsimp only [Prod.fst,Prod.snd] at hg' hcount' hlen' hw' hp' hnext'
          have hrows' : a'.weights.val.length=b'.raw.val.length := by rw [hw',hlen',hrows]
          have hf := CuSavingsRhoSourceFinish.source_success b' a'.weights hrows'
          simp only [hq,bind_tc_ok,CuSavingsRhoQuery.observe,hf] at heq
          simp only [heq]
          congr 1
          exact ih a' b' hg' hp' (by omega) (by rw [hw'];exact hl) hrows'
    · simp only [oldCalls,newCalls,hgo,if_false]

/-- Each identical source prefix can be expanded into its full ordered hash
input trace, including partial traces on rejection/failure. No hashing algebra
or collision assumption is used by this replacement. -/
theorem expanded_trace_equivalence {H Event : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (g : Array aspis_core.field.WideExact 29#usize)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry)
    (end1 : Usize) (he : end1.val ≤ 22) (hr : Canonical p.rho)
    (fuel : Nat) (a : verifier.Accumulator) (b : BatchedWeights)
    (hg : Good b []) (hp : Canonical a.power) (hc : b.terms.val ≤ a.next.val)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=b.raw.val.length) (events : Usize → List Event) :
    (oldCalls digest v p g hash obs geometry end1 fuel
      {a with weights:=CuSavingsRhoQuery.canonicalVec b}).flatMap events =
    (newCalls digest v p g hash obs geometry end1 fuel a b).flatMap events := by
  rw [calls_equivalence digest v p g hash obs geometry end1 he hr fuel a b hg hp hc hl hrows]

#print axioms calls_equivalence
#print axioms expanded_trace_equivalence
end AspisR1.CuSavingsRhoCryptographicTrace
