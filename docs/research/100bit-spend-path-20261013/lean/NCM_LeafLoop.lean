import NCM_LeafFrame

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_LeafLoop
open Aeneas Aeneas.Std Result ControlFlow MultiproofConeRef NCE_OpeningCuts
open NCE_LeafCuts Port4B_LeafStep
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

structure Ops where
  get : NCE_KeyReadCuts.Read
  reader : Reader
  request : Request
  post : Post

/-- Actual key cursor/backing/returned carrier drive the next iteration. Fuel
is the symbolic remaining-key index, never a whole native buffer unwind. -/
def run {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (ops : Ops) (kind : Usize) (batch n : Nat) :
    Nat → Array U64 16#usize → Usize → Carrier → Result (Option reference.Scratch × Carrier)
  | 0,_,cursor,s => if cursor.val < n then .div else ok (some s.scratch,s)
  | fuel+1,keys,cursor,s => if cursor.val < n then do
      let got ← NCM_LeafSelected.step D hash ops.get ops.reader ops.request ops.post kind batch s keys cursor
      match got.1 with
      | .cont state => run D hash ops kind batch n fuel got.2.2 state.2.2.2 got.2.1
      | .done _ => ok (none,got.2.1)
    else ok (some s.scratch,s)

/-- Ordered-loop invariant relates each still-unread actual key coordinate
to its selected position; the top producer/sort theorem constructs it. -/
def Stream (keys : Array U64 16#usize) (cursor : Usize)
    (q : Fin 22 → Fin 262144) (batch kind : Nat) (positions : List Nat) : Prop :=
  ∀ j, j < positions.length → keys.val[cursor.val+j]! =
    MultiproofConeSortOrder.packed q batch kind positions[j]!

/-- Exact same-carrier leaf traversal from per-step native cuts. Both a
successful optional scratch and a rejecting prefix are constructed, never
supplied. All caller fields and the complete chronological log are retained. -/
theorem observation {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (ops : Ops) (getCut : NCE_KeyReadCuts.NCE_Native_KeysRead ops.get)
    (readerCut : NCE_Native_Opening ops.reader) (leafCut : NCE_Native_Leaf ops.request ops.post)
    (kind : Usize) (batch n : Nat) (kb : kind.val < 3) (small : n ≤ 16)
    (q : Fin 22 → Fin 262144) (parsed : OraclePortCompactDraft.Parsed)
    (positions : List Nat) (keys : Array U64 16#usize) (cursor : Usize) (s : Carrier)
    (members : ∀ p ∈ positions, p ∈ OraclePortSelectedDraft.batchPositions batch)
    (stream : Stream keys cursor q batch kind.val positions)
    (span : cursor.val+positions.length = n) (room : s.scratch.n.val+positions.length ≤ 16)
    (size : s.proof.val.length = 57607) (wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val) :
    ∃ log out after,
      eval H (MultiproofConeLeafFold.leaves parsed q kind.val positions s.scratch) = (log,ok out) ∧
      run D hash ops kind batch n positions.length keys cursor s = ok (out,after) ∧
      after.prepared = s.prepared ∧ after.proof = s.proof ∧ after.log = s.log++log ∧
      (∀ t, out = some t → after.scratch = t) := by
  induction positions generalizing cursor s with
  | nil =>
    have done : ¬cursor.val < n := by simp only [List.length_nil,Nat.add_zero] at span;omega
    exact ⟨[],some s.scratch,s,rfl,by simp only [List.length_nil,run,done,if_false],rfl,rfl,by simp,by intro t eq;cases eq;rfl⟩
  | cons selected rest ih =>
    have active : cursor.val < n := by simp only [List.length_cons] at span;omega
    have cb : cursor.val < 16 := by omega
    have available : s.scratch.n.val < 16 := by simp only [List.length_cons] at room;omega
    have key : keys.val[cursor.val]! = MultiproofConeSortOrder.packed q batch kind.val selected := by
      simpa using stream 0 (by simp)
    have observed := NCM_LeafSelected.observation D hash H law ops.get getCut ops.reader readerCut ops.request ops.post leafCut
      kind batch s keys cursor cb kb available q selected (members selected (by simp)) key size parsed wire
    let input := OraclePortSelectedDraft.leaf parsed kind.val selected
    let digest := encodeState (H input)
    let nextPos := Usize.wrapping_add cursor 1#usize
    have nextVal : nextPos.val = cursor.val+1 := Port3_Wrapping.increment cursor (by omega)
    have physical := MultiproofConeLeafContent.step_exact s.scratch (MultiproofConeLeafFold.key q kind.val selected) digest available
    simp only [digest,input] at physical
    cases next : MultiproofConeLeafContent.next s.scratch (MultiproofConeLeafFold.key q kind.val selected) digest available with
    | none =>
      simp only [digest,input] at next
      let afterRead : Carrier := {s with log:=s.log++[(input,H input)]}
      refine ⟨[(input,H input)],none,afterRead,?_,?_,rfl,rfl,rfl,?_⟩
      · simp only [MultiproofConeLeafFold.leaves,eval,physical,next,input,digest]
      · simp only [List.length_cons,run,active,if_true,observed,next,input,digest,project,bind_tc_ok]
        rfl
      · intro t impossible;cases impossible
    | some nextScratch =>
      simp only [digest,input] at next
      have nextCursor := NCM_LeafFrame.next_cursor s.scratch (MultiproofConeLeafFold.key q kind.val selected) digest available nextScratch next
      have nextSize := MultiproofConeLeafFold.next_bound s.scratch (MultiproofConeLeafFold.key q kind.val selected) digest available nextScratch next
      let nextCaller : Carrier := {s with scratch:=nextScratch,log:=s.log++[(input,H input)]}
      have tailStream : Stream keys nextPos q batch kind.val rest := by
        intro j jb
        have v := stream (j+1) (by simp only [List.length_cons];omega)
        simpa only [nextVal,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem!_cons_succ] using v
      obtain ⟨log,out,after,model,native,prepared,proof,reads,final⟩ := ih nextPos nextCaller
        (fun p mem => members p (List.mem_cons_of_mem _ mem)) tailStream
        (by simp only [List.length_cons] at span;rw [nextVal];omega)
        (by simp only [List.length_cons] at room;change nextScratch.n.val+rest.length≤16;omega)
        size wire
      refine ⟨(input,H input)::log,out,after,?_,?_,prepared,proof,?_,final⟩
      · simp only [MultiproofConeLeafFold.leaves,eval,physical,next,model,input,digest,nextCaller]
      · have carrier := NCM_LeafFrame.continued {s with log:=s.log++[(input,H input)]} nextScratch nextPos nextCursor
        simp only [List.length_cons,run,active,if_true,observed,next,bind_tc_ok,project]
        simp only [project,input,nextPos,nextCaller] at carrier
        rw [carrier]
        exact native
      · simpa only [nextCaller,List.append_assoc,List.singleton_append] using reads

#print axioms observation
end AspisR1.NCM_LeafLoop
end
