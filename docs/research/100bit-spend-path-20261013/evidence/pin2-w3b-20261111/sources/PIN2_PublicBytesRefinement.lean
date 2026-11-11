import PIN2_SerializerTransport
import PIN2_SerializerLengths

/-! PIN2 W3b (2026-11-11). Discharges the `refines` hypothesis of
`PIN2_SerializerLengths` against Stream C's re-extracted body
(`PIN2_NEWGATE_r0`, source 271869c946d, file sha 92162163ae5b…).

`source_eq_program` factors the actual generated `public_bytes` as a finite
instruction list: the frozen section-9 instructions, then two raw 32-byte
extends, the `has_destination` push and (withdrawal) the destination extend.
`program_success` reads off the bytes of any successful run, and
`public_bytes_refines` identifies them with `PIN2_SerializerLengths.bytes` of
the carrier.  The only premise is successful return; there is no capacity or
allocator premise. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1.PIN2_PublicBytesRefinement
open PIN2_SerializerTransport
abbrev NewPublic := AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev NewTransition := AspisR1PublicPreparationPIN2.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Output := core.result.Result ByteVec NewError
abbrev Status := core.result.Result Unit NewError
abbrev Frontier := Array (Array U32 8#usize) 20#usize

inductive Step where
  | byte : U8 → Step
  | words : Slice U32 → Step
  | frontier : Frontier → Step
  | index : U64 → Step
  | raw : Array U8 32#usize → Step

def stepBytes : Step → List U8
  | .byte b => [b]
  | .words s => AspisR1PublicSerializer.FieldsRefinement431.encodeWords s.val
  | .frontier f => AspisR1PublicSerializer.FieldsRefinement431.encodeWords
      ((AspisR1PublicSerializer.Frontier431.rows f).flatMap (fun s => s.val))
  | .index n => (core.num.U64.to_le_bytes n).val
  | .raw a => a.val

def nextPublic (m : Result (Status × ByteVec)) (k : ByteVec → Result Output) : Result Output := do
  let (r, out) ← m
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ => k out
  | .Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      ByteVec (core.convert.FromSame NewError) residual

def program : List Step → ByteVec → Result Output
  | [], out => ok (.Ok out)
  | .byte b :: ss, out => do
    let out1 ← alloc.vec.Vec.push out b
    program ss out1
  | .words s :: ss, out =>
    nextPublic (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s)
      (program ss)
  | .frontier f :: ss, out =>
    nextPublic (AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out f)
      (program ss)
  | .index n :: ss, out => do
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
      (Array.to_slice (core.num.U64.to_le_bytes n))
    program ss out1
  | .raw a :: ss, out => do
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice a)
    program ss out1

theorem nextPublic_success (m : Result (Status × ByteVec)) (k : ByteVec → Result Output)
    (out' : ByteVec) (h : nextPublic m k = ok (.Ok out')) :
    ∃ out, m = ok (.Ok (), out) ∧ k out = ok (.Ok out') := by
  cases m with
  | fail e => simp [nextPublic] at h
  | div => simp [nextPublic] at h
  | ok r =>
    rcases r with ⟨status, out⟩
    cases status with
    | Err e =>
      simp [nextPublic, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
    | Ok u =>
      cases u
      exact ⟨out, rfl, by simpa [nextPublic, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch] using h⟩

theorem program_success (ss : List Step) (out out' : ByteVec)
    (h : program ss out = ok (.Ok out')) : out'.val = out.val ++ ss.flatMap stepBytes := by
  induction ss generalizing out with
  | nil =>
    have heq : out = out' := core.result.Result.Ok.inj (Result.ok.inj h)
    subst out'
    simp
  | cons s ss ih =>
    cases s with
    | byte b =>
      obtain ⟨out1, hp, hr⟩ := AspisR1PublicSerializer.Whole431.bind_success _ _ _ h
      have hb := AspisR1PublicSerializer.Whole431.push_success out out1 b hp
      rw [ih out1 hr, hb]
      simp [stepBytes]
    | index n =>
      obtain ⟨out1, he, hr⟩ := AspisR1PublicSerializer.Whole431.bind_success _ _ _ h
      have hb := AspisR1PublicSerializer.Success431.extend_success out out1 _ he
      rw [ih out1 hr, hb]
      simp [stepBytes, Array.to_slice]
    | raw a =>
      obtain ⟨out1, he, hr⟩ := AspisR1PublicSerializer.Whole431.bind_success _ _ _ h
      have hb := AspisR1PublicSerializer.Success431.extend_success out out1 _ he
      rw [ih out1 hr, hb]
      simp [stepBytes, Array.to_slice]
    | words s =>
      obtain ⟨out1, hf, hr⟩ := nextPublic_success _ _ _ h
      have hb := (fields_success out out1 s hf).2
      rw [ih out1 hr, hb]
      simp [stepBytes]
    | frontier f =>
      obtain ⟨out1, hf, hr⟩ := nextPublic_success _ _ _ h
      have hb := (frontier_success out out1 f hf).2
      rw [ih out1 hr, hb]
      simp [stepBytes]

def single (x : U32) : Slice U32 := Array.to_slice (Array.make 1#usize [x])

def tailSteps (t : NewTransition) : List Step :=
  [.index t.live_snapshot.next_pair_index,
   .frontier t.live_snapshot.frontier,
   .words (Array.to_slice t.candidate_afterstate.next_root),
   .frontier t.candidate_afterstate.next_frontier]

/-- The instruction list of the PIN2 body: frozen prefix, then the binding tail. -/
def steps : NewPublic → List Step
  | .Transfer p t =>
    [.byte 0#u8, .words (Array.to_slice p.anchor_root),
     .words (Array.to_slice p.nullifier), .words (single p.asset_id),
     .byte 1#u8, .words (Array.to_slice p.recipient_commitment),
     .words (Array.to_slice p.change_commitment), .byte 0#u8] ++ tailSteps t ++
    [.raw p.pool, .raw p.deployment_domain, .byte 0#u8]
  | .Withdrawal p t =>
    [.byte 1#u8, .words (Array.to_slice p.anchor_root),
     .words (Array.to_slice p.nullifier), .words (single p.asset_id),
     .byte 0#u8, .words (Array.to_slice p.change_commitment),
     .byte 1#u8, .words (single p.amount)] ++ tailSteps t ++
    [.raw p.pool, .raw p.deployment_domain, .byte 1#u8, .raw p.destination_token_account]

/-- The generated PIN2 entry point IS this instruction program, for both variants. -/
theorem source_eq_program (q : NewPublic) :
    AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      program (steps q) (alloc.vec.Vec.new U8) := by
  cases q <;> rfl

def toTransition (t : NewTransition) : AspisR1PublicSerializer.Whole431.Transition :=
  { live_snapshot :=
      { pool := t.live_snapshot.pool
        deployment_domain := t.live_snapshot.deployment_domain
        sequence := t.live_snapshot.sequence
        next_pair_index := t.live_snapshot.next_pair_index
        current_root := t.live_snapshot.current_root
        frontier := t.live_snapshot.frontier }
    candidate_afterstate :=
      { next_pair_index := t.candidate_afterstate.next_pair_index
        next_root := t.candidate_afterstate.next_root
        next_frontier := t.candidate_afterstate.next_frontier } }

/-- Field-for-field carrier map into the checked serializer's input type. -/
def toOld : NewPublic → AspisR1PublicSerializer.Whole431.Public
  | .Transfer p t => .Transfer
      { pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id,
        recipient_commitment := p.recipient_commitment,
        change_commitment := p.change_commitment } (toTransition t)
  | .Withdrawal p t => .Withdrawal
      { pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id, amount := p.amount,
        destination_token_account := p.destination_token_account,
        change_commitment := p.change_commitment } (toTransition t)

theorem steps_bytes (q : NewPublic) :
    (steps q).flatMap stepBytes = PIN2_SerializerLengths.bytes (toOld q) := by
  cases q <;>
  simp only [steps, tailSteps, single, toOld, toTransition, PIN2_SerializerLengths.bytes,
    PIN2_SerializerLengths.prefixBytes, PIN2_SerializerLengths.tailBytes,
    PIN2_SerializerLengths.pool, PIN2_SerializerLengths.domain,
    PIN2_SerializerLengths.hasDestination, PIN2_SerializerLengths.destination,
    PIN2_SerializerLengths.destinationBytes,
    AspisR1PublicSerializer.Whole431.sourceSteps, AspisR1PublicSerializer.Whole431.tailSteps,
    AspisR1PublicSerializer.Whole431.single,
    AspisR1PublicSerializer.Whole431.stepBytes, stepBytes,
    List.flatMap_cons, List.flatMap_nil, List.append_assoc,
    List.append_nil, List.cons_append, List.nil_append]

/-- `refines`, discharged: every successful run of the PIN2 extracted
`public_bytes` returns exactly the PIN2 byte image of its carrier. -/
theorem public_bytes_refines (q : NewPublic) (out : ByteVec)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) :
    out.val = PIN2_SerializerLengths.bytes (toOld q) := by
  rw [source_eq_program] at h
  have hs := program_success _ _ out h
  rw [hs, steps_bytes]
  rfl

theorem public_bytes_length (q : NewPublic) (out : ByteVec)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) :
    out.val.length = match q with | .Transfer _ _ => 1520 | .Withdrawal _ _ => 1524 := by
  rw [public_bytes_refines q out h, PIN2_SerializerLengths.length]
  cases q <;> rfl

#print axioms nextPublic_success
#print axioms program_success
#print axioms source_eq_program
#print axioms steps_bytes
#print axioms public_bytes_refines
#print axioms public_bytes_length
end AspisR1.PIN2_PublicBytesRefinement
