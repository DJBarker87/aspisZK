import R1Z.ProverCommitPublication33
import R1Z.ProverCommitMerge33
/-! Byte publication control. Codec and multiproof calls remain explicit
results, including errors; no success law for those callees is postulated.
This is a local caller theorem, not a complete source experiment. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPublish43
abbrev Bytes := List UInt8
inductive Error where
  | semantic | parse | merkle | transcript
  deriving DecidableEq

structure QueryParts where
  c1 : Bytes
  c2 : Bytes
  salt1 : Bytes
  salt2 : Bytes
  folded : Bytes
  saltf : Bytes

def queryStep (out : Bytes) (p : QueryParts) : Bytes :=
  out ++ p.c1 ++ p.c2 ++ p.salt1 ++ p.salt2 ++ p.folded ++ p.saltf

def queryBytes (p : QueryParts) : Bytes :=
  p.c1 ++ p.c2 ++ p.salt1 ++ p.salt2 ++ p.folded ++ p.saltf

theorem query_step (out : Bytes) (p : QueryParts) :
    queryStep out p = out ++ queryBytes p := by
  simp only [queryStep,queryBytes,List.append_assoc]

def queries : List QueryParts → Bytes → Bytes
  | [],out => out
  | p::ps,out => queries ps (queryStep out p)

theorem query_loop (ps : List QueryParts) (out : Bytes) :
    ps.foldl queryStep out = queries ps out := by
  induction ps generalizing out with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem query_exact (ps : List QueryParts) (out : Bytes) :
    queries ps out = out ++ (ps.map queryBytes).flatten := by
  induction ps generalizing out with
  | nil => simp only [queries,List.map_nil,List.flatten_nil,List.append_nil]
  | cons p ps ih =>
    rw [queries,ih,query_step]
    simp only [List.map_cons,List.flatten_cons,List.append_assoc]

structure Slot where
  nodes : Except Error Bytes
  cap : Nat

def appendSlot (out : Bytes) (slot : Slot) : Except Error Bytes := do
  let nodes ← slot.nodes
  if nodes.length > slot.cap then .error .parse
  else .ok (out ++ nodes ++ List.replicate (slot.cap-nodes.length) 0)

theorem slot_length (out : Bytes) (slot : Slot) (result : Bytes)
    (ok : appendSlot out slot = .ok result) : result.length=out.length+slot.cap := by
  unfold appendSlot at ok
  cases hn : slot.nodes with
  | error e => simp only [hn,bind,Except.bind] at ok; cases ok
  | ok nodes =>
    simp only [hn,bind,Except.bind] at ok
    split at ok
    · cases ok
    · cases ok
      simp only [List.length_append,List.length_replicate]
      omega

def slots : List Slot → Bytes → Except Error Bytes
  | [],out => .ok out
  | s::ss,out => (appendSlot out s).bind (slots ss)

def slotLoop (ss : List Slot) (out : Bytes) : Except Error Bytes :=
  ss.foldl (fun result slot => result.bind (fun bytes => appendSlot bytes slot)) (.ok out)

theorem slots_loop (ss : List Slot) (out : Bytes) : slotLoop ss out = slots ss out := by
  have aux : ∀ ss (initial : Except Error Bytes),
      ss.foldl (fun result slot => result.bind (fun bytes => appendSlot bytes slot)) initial =
        initial.bind (slots ss) := by
    intro ss
    induction ss with
    | nil => intro initial; cases initial <;> rfl
    | cons s ss ih =>
      intro initial
      cases initial with
      | error e => exact ih (.error e)
      | ok bytes => exact ih (appendSlot bytes s)
  exact aux ss (.ok out)

theorem slots_length (ss : List Slot) (out result : Bytes)
    (ok : slots ss out = .ok result) :
    result.length=out.length+(ss.map Slot.cap).sum := by
  induction ss generalizing out with
  | nil => cases ok; simp only [List.map_nil,List.sum_nil,Nat.add_zero]
  | cons s ss ih =>
    simp only [slots] at ok
    cases hs : appendSlot out s with
    | error e => simp only [hs,Except.bind] at ok; cases ok
    | ok next =>
      simp only [hs,Except.bind] at ok
      have hlen := slot_length out s next hs
      have htail := ih next ok
      simp only [List.map_cons,List.sum_cons]
      omega

/-- Both byte-length guards and every prior node error survive unchanged. -/
def assemble (front : Except Error Bytes) (ps : List QueryParts)
    (ss : List Slot) (offNodes proofBytes : Nat) : Except Error Bytes := do
  let front ← front
  let out := queries ps front
  if out.length ≠ offNodes then .error .parse else do
    let out ← slots ss out
    if out.length ≠ proofBytes then .error .parse else .ok out

def assembleLoop (front : Except Error Bytes) (ps : List QueryParts)
    (ss : List Slot) (offNodes proofBytes : Nat) : Except Error Bytes := do
  let front ← front
  let out := ps.foldl queryStep front
  if out.length ≠ offNodes then .error .parse else do
    let out ← slotLoop ss out
    if out.length ≠ proofBytes then .error .parse else .ok out

theorem assemble_loop (front : Except Error Bytes) (ps : List QueryParts)
    (ss : List Slot) (offNodes proofBytes : Nat) :
    assembleLoop front ps ss offNodes proofBytes = assemble front ps ss offNodes proofBytes := by
  simp only [assembleLoop,assemble,query_loop,slots_loop]

/-- Finalisation follows the native order: replay, transcript guard, Merkle
collision guard, then first-conflict ordered merge. Errors contain no proof. -/
def finish {Table : Type} (proof : Except Error Bytes) (replay : Except Error Bool)
    (collision : Bool) (merge : Except Error Table) : Except Error (Bytes × Table) := do
  let proof ← proof
  let agrees ← replay
  if !agrees then .error .transcript else
    if collision then .error .merkle else do
      let table ← merge
      .ok (proof,table)

theorem proof_error {Table : Type} (e : Error) (replay : Except Error Bool)
    (collision : Bool) (merge : Except Error Table) :
    finish (.error e) replay collision merge = .error e := rfl

theorem replay_error {Table : Type} (proof : Bytes) (e : Error)
    (collision : Bool) (merge : Except Error Table) :
    finish (.ok proof) (.error e) collision merge = .error e := rfl

theorem replay_disagreement {Table : Type} (proof : Bytes)
    (collision : Bool) (merge : Except Error Table) :
    finish (.ok proof) (.ok false) collision merge = .error .transcript := rfl

theorem merkle_collision {Table : Type} (proof : Bytes) (merge : Except Error Table) :
    finish (.ok proof) (.ok true) true merge = .error .merkle := rfl

theorem merge_error {Table : Type} (proof : Bytes) (e : Error) :
    finish (.ok proof) (.ok true) false (.error e : Except Error Table) = .error e := rfl

#print axioms query_step
#print axioms query_loop
#print axioms query_exact
#print axioms slot_length
#print axioms slots_loop
#print axioms slots_length
#print axioms assemble_loop
#print axioms proof_error
#print axioms replay_error
#print axioms replay_disagreement
#print axioms merkle_collision
#print axioms merge_error
end R1Z.ProverCommitPublish43
