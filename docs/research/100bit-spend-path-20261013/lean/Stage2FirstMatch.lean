import Stage2QueryChecks
import R1MatchingSupport
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2FirstMatch
open AspisR1Stage2 AspisCircleGroupOrder
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod P) F]

/-- R13 authenticated leaf/word identification, S4/S5 dot semantics and S7
geometry/circle arithmetic. No accepted-query or match0 premise is present. -/
structure QueryLaws (ops : QueryOps) (decode : Stage2E → F)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
    (geometry : verifier.QueryGeometry) (d : MatchingSupport.Data F)
    (q : Fin 22 → Fin 262144) : Prop where
  compare : ∀ x y, ops.ne x y = ok false → decode x = decode y
  fold : ∀ (a : verifier.Accumulator) bytes dots inv alpha folded,
    ops.opening proof a.next = ok bytes → ops.dots bytes g = ok dots →
    ops.inverse geometry a.next = ok inv → Array.index_usize p.alpha 0#usize = ok alpha →
    ops.circle alpha dots inv = ok folded →
    ∀ j : Fin 22, j.val = a.next.val →
      decode folded = FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord d.W d.gamma) (q j)
  value : ∀ (a : verifier.Accumulator) index u bytes values slot value,
    Array.index_usize p.queries a.next = ok index → lift (UScalar.cast .Usize index) = ok u →
    ops.opening proof a.next = ok bytes → ops.values bytes = ok values →
    u % 4#usize = ok slot → Array.index_usize values slot = ok value →
    ∀ j : Fin 22, j.val = a.next.val → decode value = d.V (q j)

theorem successful_query_match (aops : AccumulateOps) (ops : QueryOps)
    (decode : Stage2E → F) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (d : MatchingSupport.Data F)
    (q : Fin 22 → Fin 262144) (laws : QueryLaws ops decode proof p g geometry d q)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.queryWithOps aops ops proof p a g obs geometry b = ok (.Ok (out,bout))) :
    ∀ j : Fin 22, j.val = a.next.val → MatchingSupport.match0 d (q j) := by
  obtain ⟨index,u,bytes,dots,inv,alpha,folded,values,slot,value,
    hi,hu,hb,hd,hinv,ha,hf,hv,hs,hvalue,hne⟩ :=
    Stage2Finish.query_first_comparison aops ops proof p a out g obs geometry b bout h
  intro j hj
  exact (laws.fold a bytes dots inv alpha folded hb hd hinv ha hf j hj).symm.trans
    ((laws.compare folded value hne).trans (laws.value a index u bytes values slot value hi hu hb hv hs hvalue j hj))

def Prefix (d : MatchingSupport.Data F) (q : Fin 22 → Fin 262144)
    (a : verifier.Accumulator) : Prop :=
  ∀ j : Fin 22, j.val < a.next.val → MatchingSupport.match0 d (q j)

theorem prefix_step (d : MatchingSupport.Data F) (q : Fin 22 → Fin 262144)
    (a out : verifier.Accumulator) (advance : out.next.val = a.next.val + 1)
    (hprefix : Prefix d q a)
    (matched : ∀ j : Fin 22, j.val = a.next.val → MatchingSupport.match0 d (q j)) :
    Prefix d q out := by
  intro j hj
  by_cases before : j.val < a.next.val
  · exact hprefix j before
  · exact matched j (by omega)

/-- The saved ten checks are named R15/R13 premises; the twelve resumed
checks follow from successful calls and the leaf/fold laws above. -/
theorem twelve_queries_firstMatch (aops : AccumulateOps) (ops : QueryOps)
    (decode : Stage2E → F) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (d : MatchingSupport.Data F)
    (q : Fin 22 → Fin 262144) (laws : QueryLaws ops decode proof p g geometry d q)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (start : a.next.val = 10) (saved_R15_R13 : Prefix d q a)
    (h : verifier.candidate.query_loop (stage2QueryCall aops ops)
      proof p a g obs geometry b 22#usize = ok (.Ok (out,bout))) :
    ∀ j, MatchingSupport.match0 d (q j) := by
  have step : ∀ a b a1 b1, a.next.val < 22 →
      Stage2ContinuationOwnedLoop.adapt (fun a b => stage2QueryCall aops ops proof p a g obs geometry b)
        a b = ok (.Ok (),a1,b1) → Prefix d q a → Prefix d q a1 := by
    intro a b a1 b1 active hc hp
    unfold Stage2ContinuationOwnedLoop.adapt at hc
    obtain ⟨r, hr, hc⟩ := Stage2Finish.bind_success _ _ _ hc
    cases r with
    | Err e => cases hc
    | Ok pair =>
      rcases pair with ⟨a2,b2⟩
      cases Result.ok.inj hc
      exact prefix_step d q a a1 (query_next aops ops proof p a a1 g obs geometry b b1 hr) hp
        (successful_query_match aops ops decode proof p g obs geometry d q laws a a1 b b1 hr)
  obtain ⟨hprefix,he⟩ := Stage2Finish.twelve_calls_invariant aops ops proof p g obs geometry
    (fun a _ => Prefix d q a) step a out b bout start saved_R15_R13 h
  intro j
  exact hprefix j (by rw [he]; exact j.isLt)

#print axioms successful_query_match
#print axioms prefix_step
#print axioms twelve_queries_firstMatch
end AspisR1.Stage2FirstMatch
end
