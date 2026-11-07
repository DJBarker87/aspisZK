import NMM_LaneScalarLoop
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneScalarSource
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
attribute [local instance] Classical.propDecidable
abbrev Lane := NMM_LaneTranscription.Lane
abbrev PE := NMM_LaneTranscription.PE

structure Fields where
 bump : U8
 master : Option U8
 lane : U8
 next : U64
 root : Option U32
 frontier : Option U32

def project (byte : Fin 32) (level : Fin 20) (word : Fin 8) (out : Lane) : Fields :=
 ⟨out.bump,out.master.val[byte.val]?,out.lane_id,out.tree.next_leaf_index,
 out.tree.root.val[word.val]?,
 (out.tree.frontier.val[level.val]?).bind (fun node => node.val[word.val]?)⟩

def mapOut (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 core.result.Result Lane PE → core.result.Result Fields PE
 | .Err e => .Err e
 | .Ok out => .Ok (project byte level word out)

def finish (byte : Fin 32) (level : Fin 20) (word : Fin 8)
 (bump : U8) (master : Array U8 32#usize) (lane : U8) (next : U64)
 (root emptyRoot : Node) (loop : Reply × U32 × List (Fin 20)) : core.result.Result Fields PE :=
 match loop.1 with
 | .Err e => .Err e
 | .Ok _ =>
  if next.val=0 ∧ root≠emptyRoot then .Err .InvalidAccountData
  else .Ok ⟨bump,master.val[byte.val]?,lane,next,some (root word),some loop.2.1⟩

theorem make_projection (byte : Fin 32) (level : Fin 20) (word : Fin 8)
 (bump : U8) (master : Array U8 32#usize) (lane : U8) (next : U64)
 (root : Node) (state : Frontier) :
 project byte level word (NKP_LaneCarrier.make bump master lane next root state) =
 ⟨bump,master.val[byte.val]?,lane,next,some (root word),some (state level word)⟩ := by
 unfold project
 change Fields.mk bump (master.val[byte.val]?) lane next
  ((NKP_LaneCarrier.node root).val[word.val]?)
  (((NKP_LaneCarrier.frontier state).val[level.val]?).bind (fun node => node.val[word.val]?)) = _
 rw [NKP_LaneCarrier.node_at,NKP_LaneCarrier.frontier_at,Option.bind_some,NKP_LaneCarrier.node_at]

theorem completion_projection (byte : Fin 32) (level : Fin 20) (word : Fin 8)
 (bump : U8) (master : Array U8 32#usize) (lane : U8) (next : U64)
 (root emptyRoot : Node) (loop : Reply × Frontier × List (Fin 20)) :
 mapOut byte level word (NKP_LaneCompletion.finish bump master lane next root emptyRoot loop).1 =
 finish byte level word bump master lane next root emptyRoot (NMM_LaneScalarLoop.observe level word loop) := by
 rcases loop with ⟨reply,state,calls⟩
 cases reply with
 | Err e => rfl
 | Ok u =>
  cases u
  by_cases bad : next.val=0 ∧ root≠emptyRoot
  · simp only [NKP_LaneCompletion.finish,finish,NMM_LaneScalarLoop.observe,if_pos bad,mapOut]
  · simp only [NKP_LaneCompletion.finish,finish,NMM_LaneScalarLoop.observe,if_neg bad,mapOut]
    rw [make_projection]

def body (p : NLK_LaneInput.Sized) (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 core.result.Result Fields PE :=
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => .Err e
 | .Ok f =>
  match NLK_LaneDigest.decode (NLK_LaneInput.root p) with
  | .Err _ => .Err .InvalidAccountData
  | .Ok root =>
   finish byte level word f.bump f.master f.lane f.next root NLK_LaneTable.final
    (NMM_LaneScalarLoop.run NLK_LaneTable.empty (NLK_LaneLoop.occupied f.next)
      (NLK_LaneLoop.raw p) level word NLK_LaneLoop.levels
      (NLK_LaneLoop.zero level word))

theorem body_projection (p : NLK_LaneInput.Sized)
 (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 mapOut byte level word (NLK_LaneProgram.body p) = body p byte level word := by
 unfold NLK_LaneProgram.body body
 cases h : NLK_LaneHeader.sourcePrefix p with
 | Err e => rfl
 | Ok f =>
  cases r : NLK_LaneDigest.decode (NLK_LaneInput.root p) with
  | Err e => rfl
  | Ok root => rw [completion_projection,NMM_LaneScalarLoop.loop_projection]

def value (bytes : Slice U8) (byte : Fin 32) (level : Fin 20) (word : Fin 8) :=
 if h : bytes.val.length=768 then body ⟨bytes,h⟩ byte level word else (.Err .InvalidAccountData : core.result.Result Fields PE)

theorem canonical (bytes : Slice U8) (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 value bytes byte level word = mapOut byte level word (NLK_LaneProgram.referenceValue bytes) := by
 unfold value NLK_LaneProgram.referenceValue
 split
 · exact (body_projection _ byte level word).symm
 · rfl

/-- All scalar windows recover the full typed Box payload. This reuses the
predecessor's constructor/frame proof rather than postulating record equality. -/
theorem windows_complete (a b : Lane)
 (windows : ∀ byte : Fin 32, ∀ level : Fin 20, ∀ word : Fin 8,
  project byte level word a = project byte level word b) : a = b := by
 apply NKF_LaneConstructor.constructor a b
 constructor
 · exact congrArg Fields.bump (windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩)
 · intro i hi
   exact congrArg Fields.master (windows ⟨i,hi⟩ ⟨0,by omega⟩ ⟨0,by omega⟩)
 · exact congrArg Fields.lane (windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩)
 · exact congrArg Fields.next (windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩)
 · intro i hi
   exact congrArg Fields.root (windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨i%8,Nat.mod_lt _ (by omega)⟩)
 · intro i ha hb j hj
   have small : i<20 := by
    have h:=a.tree.frontier.property
    change a.tree.frontier.val.length = 20 at h
    omega
   have h := congrArg Fields.frontier
    (windows ⟨0,by omega⟩ ⟨i,small⟩ ⟨j%8,Nat.mod_lt _ (by omega)⟩)
   simpa only [project,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.bind_some] using h

theorem results_complete (a b : core.result.Result Lane PE)
 (windows : ∀ byte : Fin 32, ∀ level : Fin 20, ∀ word : Fin 8,
  mapOut byte level word a = mapOut byte level word b) : a = b := by
 cases a with
 | Err e =>
  cases b with
  | Err f =>
   have h := windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩
   change core.result.Result.Err e = core.result.Result.Err f at h
   have same : e=f := core.result.Result.Err.inj h
   cases same;rfl
  | Ok value =>
   have h := windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩
   cases h
 | Ok value =>
  cases b with
  | Err e =>
   have h := windows ⟨0,by omega⟩ ⟨0,by omega⟩ ⟨0,by omega⟩
   cases h
  | Ok other =>
   congr 1
   apply windows_complete value other
   intro byte level word
   exact core.result.Result.Ok.inj (windows byte level word)

#print windows_complete
#print axioms windows_complete
#print results_complete
#print axioms results_complete

#print make_projection
#print axioms make_projection
#print completion_projection
#print axioms completion_projection
#print body_projection
#print axioms body_projection
#print canonical
#print axioms canonical
end NMM_LaneScalarSource
