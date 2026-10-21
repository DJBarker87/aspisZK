import MultiproofConeRootGuard

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConePhysicalVerify
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConePhysicalViews
open MultiproofConePhysicalFrozenLevels MultiproofConeNodeDomain MultiproofConeNodeIteration
open MultiproofConeLevelIteration MultiproofConeLivePreservation MultiproofConeRootGuard
open OraclePortFrozenOrder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def finish (root : Digest) (physical : Slice U8) : Result reference.Level → Bool
  | .ok (.Done s) => sourceRoot root physical s
  | _ => false

/-- Instrumented source binary verifier after the pure initial checks. -/
def verify (root : Digest) (physical : Slice U8) (s : reference.Scratch) : Program Bytes State Bool :=
  if wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0 then
    bind (transport (MultiproofConePhysicalLevels.levels 18 s physical))
      (fun result => .done (finish root physical result))
  else .done false

theorem strict_of_live (s : reference.Scratch)
    (order : ((live s 0 s.n.val).map Prod.fst).Pairwise (·<·)) :
    MultiproofConeLiveOrder.Strict (keys s) 0 s.n.val := by
  intro a b _ ab bn
  have length : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by simp [live_length]
  have eq := List.pairwise_iff_getElem.mp order a b (by omega) (by omega) ab
  simpa only [live,MultiproofConePhysicalLive.view,List.map_map,List.getElem_map,
    List.getElem_range,Function.comp_apply,decodeEntry,MultiproofConePhysicalLive.cell,
    Nat.zero_add,keys] using eq

/-- Accepted physical verification, including root and exact node consumption,
has the frozen verifier's complete ordered log and Bool. The successful
extracted height result is derived from source acceptance, not a premise. -/
theorem accepted_verify {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (root : Digest) (physical : Slice U8) (s : reference.Scratch)
    (zero : s.«at».val=0) (accepted : (eval H (verify root physical s)).2=true) :
    eval H (verify root physical s)=
      eval H (verifyInPlace (decodeState root) (live s 0 s.n.val) (remaining physical s.«at»)) := by
  by_cases guard : wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0
  · have size : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by simp [live_length]
    have domain : Domain physical s := by
      refine ⟨?_,?_,by omega⟩
      · by_contra bad
        have empty : (live s 0 s.n.val).map Prod.fst=[] := by
          apply List.length_eq_zero_iff.mp;omega
        exact guard.1.1 empty
      · have bound := guard.1.2.1;omega
    have sorted := strict_of_live s guard.1.2.2.1
    have physicalResult : (eval H (transport (MultiproofConePhysicalLevels.levels 18 s physical))).2 =
        iterate (fun s => reference.level_rows D hash s physical 0#usize 0#usize) 18 s := by
      rw [transport_observation]
      exact MultiproofConePhysicalLevels.levels_result D hash (rawOracle H) law 18 s physical domain
    simp only [verify,if_pos guard,eval_bind,eval] at accepted
    cases result : iterate (fun s => reference.level_rows D hash s physical 0#usize 0#usize) 18 s with
    | fail e => simp only [physicalResult,result,finish] at accepted;cases accepted
    | div => simp only [physicalResult,result,finish] at accepted;cases accepted
    | ok out =>
      cases out with
      | Stop stopped => simp only [physicalResult,result,finish] at accepted;cases accepted
      | Done final =>
        have rootOK : sourceRoot root physical final=true := by
          simpa only [physicalResult,result,finish] using accepted
        have atBound : final.«at».val≤physical.val.length := by
          have facts := of_decide_eq_true rootOK
          exact Nat.le_of_eq facts.2.2.2
        obtain ⟨log,source,target⟩ := levels_join D hash H law physical 18 s final domain sorted result
        have finalGuard := root_guard root physical final atBound
        have sourceEval : eval H (verify root physical s)=
            (log.map (fun e => (flatten e.1,decodeState e.2)),true) := by
          simp only [verify,if_pos guard,eval_bind,transport_observation,source,eval,finish,rootOK,List.append_nil]
        have nodesLength : (remaining physical s.«at»).length=physical.val.length := by
          simp only [remaining,MultiproofConeCanonical.bytesOf,List.length_map,List.length_drop,zero,Nat.sub_zero]
        have modelGuard : wellFormed ((live s 0 s.n.val).map Prod.fst) ∧
            (remaining physical s.«at»).length%32=0 := by rw [nodesLength];exact guard
        rw [sourceEval]
        simp only [verifyInPlace,if_pos modelGuard,eval_bind,target,eval,List.append_nil]
        change (_,true)=(_,modelRoot (decodeState root) (some (live final 0 final.n.val,remaining physical final.«at»)))
        rw [←finalGuard,rootOK]
  · simp only [verify,if_neg guard,eval] at accepted;cases accepted

#print axioms strict_of_live
#print axioms accepted_verify
end AspisR1.MultiproofConePhysicalVerify
end
