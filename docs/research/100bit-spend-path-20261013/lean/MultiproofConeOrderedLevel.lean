import MultiproofConeLiveFold

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeOrderedLevel
open OraclePortFrozenOrder OracleDecisionMultiTree
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

/-- Logical live-list projection of binary_group, retaining its XOR guard.
This is an instrumented logical reference, not a physical scratch adoption. -/
def sourceLevel : Nat → Live → Bytes → Program Bytes State (Option (Live × Bytes))
  | 0,_,nodes => .done (some ([],nodes))
  | _+1,[],nodes => .done (some ([],nodes))
  | fuel+1,(i,v)::rest,nodes =>
      let both := match rest with | (j,_)::_ => decide (j=i^^^1) | [] => false
      if both then
        let right := (rest.head!).2
        .ask (BinMerkle32Path.nodeInput (children v right)) fun d =>
          bind (sourceLevel fuel (rest.drop 1) nodes) fun out =>
            .done (out.map fun x => ((i/2,d)::x.1,x.2))
      else match SemanticRecordCodec.decodeState (nodes.take 32) with
        | none => .done none
        | some sibling =>
          let pair := if i%2=0 then children v sibling else children sibling v
          .ask (BinMerkle32Path.nodeInput pair) fun d =>
            bind (sourceLevel fuel rest (nodes.drop 32)) fun out =>
              .done (out.map fun x => ((i/2,d)::x.1,x.2))

/-- Exact Program identity, not just equal final roots or acceptance. Every
hash request, continuation, duplicate address and short-sibling rejection is
retained, on arbitrary ascending live lists and arbitrary supplied bytes. -/
theorem level_program (fuel : Nat) (live : Live) (nodes : Bytes)
    (sorted : (live.map Prod.fst).Pairwise (·<·)) :
    sourceLevel fuel live nodes=runLevel fuel live nodes := by
  induction fuel generalizing live nodes with
  | zero => rfl
  | succ fuel ih =>
    cases live with
    | nil => rfl
    | cons head rest =>
      rcases head with ⟨i,v⟩
      have tailSorted : (rest.map Prod.fst).Pairwise (·<·) :=
        (List.pairwise_cons.mp sorted).2
      have dropSorted : ((rest.drop 1).map Prod.fst).Pairwise (·<·) := by
        rw [List.map_drop]
        exact tailSorted.drop
      have guard : (match rest with | (j,_)::_ => decide (j=i^^^1) | [] => false) =
          (match rest with | (j,_)::_ => decide (paired i j) | [] => false) := by
        cases rest with
        | nil => rfl
        | cons head tail =>
          rcases head with ⟨j,w⟩
          have asc : i<j := (List.pairwise_cons.mp sorted).1 j (by simp)
          simp only [MultiproofConeModelBoundary.paired_iff i j asc]
      simp only [sourceLevel,runLevel,guard,ih _ _ tailSorted,ih _ _ dropSorted]
      cases rest <;> rfl

/-- Exact ordered read/answer observations follow for every oracle, without
any assumption about collision freedom or distinct hash addresses. -/
theorem level_log (H : Bytes → State) (fuel : Nat) (live : Live) (nodes : Bytes)
    (sorted : (live.map Prod.fst).Pairwise (·<·)) :
    eval H (sourceLevel fuel live nodes)=eval H (runLevel fuel live nodes) := by
  rw [level_program fuel live nodes sorted]

#print axioms level_program
#print axioms level_log
end AspisR1.MultiproofConeOrderedLevel
end
