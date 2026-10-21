import MultiproofConeSlotTail

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeVerifyState
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalViews MultiproofConePhysicalTransport
open MultiproofConePhysicalVerify MultiproofConeSlotTail
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem eval_map {α β : Type} (H : Bytes → State) (p : Program Bytes State α) (f : α → β) :
    eval H (bind p (fun x => .done (f x)))=((eval H p).1,f (eval H p).2) := by
  simp only [eval_bind,eval,List.append_nil]

def finishState (root : Digest) (physical : Slice U8) (initial : reference.Scratch) :
    Result reference.Level → Bool × reference.Scratch
  | .ok (.Done s) => (MultiproofConeRootGuard.sourceRoot root physical s,s)
  | .ok (.Stop s) => (false,s)
  | _ => (false,initial)

def verifyState (root : Digest) (physical : Slice U8) (s : reference.Scratch) :
    Program Bytes State (Bool × reference.Scratch) :=
  if wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0 then
    bind (transport (MultiproofConePhysicalLevels.levels 18 s physical))
      (fun result => .done (finishState root physical s result))
  else .done (false,s)

/-- Exact physical scratch is threaded across successful slots. Erasing it
commutes with observation, so arbitrary suffix data cannot be silently reset. -/
theorem verify_projection (H : Bytes → State) (root : Digest) (physical : Slice U8)
    (s : reference.Scratch) :
    ((eval H (verifyState root physical s)).1,(eval H (verifyState root physical s)).2.1)=
      eval H (MultiproofConePhysicalVerify.verify root physical s) := by
  unfold verifyState MultiproofConePhysicalVerify.verify
  split
  · simp only [eval_bind,eval,List.append_nil]
    cases (eval H (transport (MultiproofConePhysicalLevels.levels 18 s physical))).2 with
    | fail e => rfl
    | div => rfl
    | ok out => cases out <;> rfl
  · rfl

def tailState (p : Parsed) (batch kind : Nat) (nodes : Slice U8) (s : reference.Scratch) :
    Program Bytes State (Bool × reference.Scratch) :=
  let is := (live s 0 s.n.val).map Prod.fst
  if wellFormed is then
    let count := MultiproofConeCountLevels.sourceCount 18 is
    let cap := capacity (3*batch+kind)
    let bs := MultiproofConeCanonical.bytesOf nodes.val
    if count≤cap ∧ bs.length=32*cap ∧
        MultiproofConePadding.scan (4*(cap-count)) (bs.drop (32*count))=true then
      verifyState (encodeState (OraclePortBatchDraft.committedRoot p kind))
        (prefixNodes nodes count) {s with «at»:=0#usize}
    else .done (false,s)
  else .done (false,s)

theorem tail_projection (H : Bytes → State) (p : Parsed) (batch kind : Nat)
    (nodes : Slice U8) (s : reference.Scratch) :
    ((eval H (tailState p batch kind nodes s)).1,(eval H (tailState p batch kind nodes s)).2.1)=
      eval H (tail p batch kind nodes s) := by
  unfold tailState tail
  dsimp only
  split
  · split
    · exact verify_projection H _ _ _
    · rfl
  · rfl

#print axioms eval_map
#print axioms verify_projection
#print axioms tail_projection
end AspisR1.MultiproofConeVerifyState
end
