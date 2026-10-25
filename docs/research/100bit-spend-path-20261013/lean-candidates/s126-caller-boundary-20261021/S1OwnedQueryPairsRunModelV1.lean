import S1OwnedQueryPairsStepModelV1
import R4Transport2ScanComposition
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.Q22WordScan AspisV8R19.SqueezeOracleBridge

def index (k : Fin 8) : Usize := Usize.ofNatCore k.val (by have := k.isLt;scalar_tac)
theorem index_bound (k : Fin 8) : (index k).val<8 := by simp [index]

def pairsOf (ks : List (Fin 8)) (blocks advances : Blocks) : List (State × State) :=
  ks.map (fun k => (decodeState (atBlock blocks (index k) (index_bound k)),
    decodeState (atBlock advances (index k) (index_bound k))))

def sourcePairs (s : ScanState) : List (State × State) → State → Except Nat (List Nat) × State
  | [],fallback => (finish s,fallback)
  | (block,advanced)::ps,fallback =>
    let r:=scan s (AspisV8R19.SamplerWords.words 18 block)
    if r.2 then (finish r.1,advanced) else sourcePairs r.1 ps fallback

def lastAdvance : List (State × State) → State → State
  | [],fallback => fallback
  | (_,advanced)::ps,_ => lastAdvance ps advanced

/-- Source's fixed final fallback and the retained mathematical pairs driver
agree when the fallback is the last materialized advance. No distinctness of
advance states or successful scan is assumed. -/
theorem sourcePairs_eq_pairsRun (ps : List (State × State)) (s : ScanState) (fallback : State) :
    sourcePairs s ps (lastAdvance ps fallback)=
      AspisR1.R4Transport2ScanComposition.pairsRun s ps fallback := by
  induction ps generalizing s fallback with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨block,advanced⟩
    simp only [lastAdvance,sourcePairs,AspisR1.R4Transport2ScanComposition.pairsRun]
    split
    · rfl
    · exact ih _ advanced

/-- Analysis device over the same emitted step; it returns the actual final
full state so the source finisher and exact error can be composed separately. -/
def walk : List (Fin 8) → OwnedScan → Block → Blocks → Blocks → Result (OwnedScan × Block)
  | [],s,state,_,_ => ok (s,state)
  | k::ks,s,state,blocks,advances => do
    let (after,next,stop) ← pairs_step s state (index k) blocks advances
    if stop then ok (after,next) else walk ks after next blocks advances

/-- TOTAL complete-state scan walk, including stopped and exhausted paths.
Every actual child call and its invariant is derived from the fixed block
model. There is no scanner/driver-law or successful-child premise. -/
theorem walk_model (ks : List (Fin 8)) (s : OwnedScan) (state : Block)
    (blocks advances : Blocks) (valid : Valid s) :
    ∃ (sf : OwnedScan) (selected : Block),
      walk ks s state blocks advances=ok (sf,selected) ∧ Valid sf ∧
      sourcePairs (qState s) (pairsOf ks blocks advances) (decodeState state)=
        (finish (qState sf),decodeState selected) := by
  induction ks generalizing s state with
  | nil => exact ⟨s,state,rfl,valid,rfl⟩
  | cons k ks ih =>
    obtain ⟨after,next,stop,called,validAfter,scanned,selected⟩ :=
      step_model s state (index k) blocks advances (index_bound k) valid
    cases stop with
    | true =>
      refine ⟨after,next,?_,validAfter,?_⟩
      · simp only [walk,called,bind_tc_ok]
        rfl
      · simp only [pairsOf,List.map_cons,sourcePairs,scanned]
        rw [selected]
        rfl
    | false =>
      obtain ⟨sf,selectedFinal,tailCall,validFinal,tailModel⟩ := ih after next validAfter
      refine ⟨sf,selectedFinal,?_,validFinal,?_⟩
      · simp only [walk,called,bind_tc_ok,Bool.false_eq_true,if_false]
        exact tailCall
      · simp only [pairsOf,List.map_cons,sourcePairs,scanned,Bool.false_eq_true,if_false]
        have nextEq : next=state := selected
        rw [nextEq] at tailModel
        exact tailModel

#print axioms sourcePairs_eq_pairsRun
#print axioms walk_model
end AspisS1OwnedQueryPairs.Model
