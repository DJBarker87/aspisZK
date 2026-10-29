import R1Z.ProverCommitPublicFrontier34

/-! Successful-return refinement of the actual extracted public_bytes entry.
The finite instruction list is only a factoring device: source_eq_program
connects it by equality to the generated definition for both source variants.
No Rust runtime, allocator-success or cross-toolchain integration claim. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicSerializer.Whole431
open FieldsRefinement431 Success431 Frontier431
open pool_v1.pair_forest_semantic_terminal
open pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

abbrev Public := r0.Public
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev Transition := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Output := core.result.Result ByteVec PublicError

inductive Step where
  | byte : Std.U8 → Step
  | words : Slice Field → Step
  | frontier : Frontier → Step
  | index : Std.U64 → Step

def stepWords : Step → List Field
  | .byte _ => []
  | .words s => s.val
  | .frontier f => (rows f).flatMap (fun s => s.val)
  | .index _ => []

def stepBytes : Step → List Std.U8
  | .byte b => [b]
  | .words s => encodeWords s.val
  | .frontier f => encodeWords ((rows f).flatMap (fun s => s.val))
  | .index n => (core.num.U64.to_le_bytes n).val

def nextPublic (m : Result (Status × ByteVec))
    (k : ByteVec → Result Output) : Result Output := do
  let (r, out) ← m
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ => k out
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ByteVec (core.convert.FromSame PublicError) residual

def program : List Step → ByteVec → Result Output
  | [], out => ok (.Ok out)
  | .byte b :: ss, out => do
    let out1 ← alloc.vec.Vec.push out b
    program ss out1
  | .words s :: ss, out => nextPublic (fields out s) (program ss)
  | .frontier f :: ss, out => nextPublic (frontier out f) (program ss)
  | .index n :: ss, out => do
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
      (Array.to_slice (core.num.U64.to_le_bytes n))
    program ss out1

theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem push_success (out out' : ByteVec) (b : Std.U8)
    (h : alloc.vec.Vec.push out b = ok out') :
    out'.val = out.val ++ [b] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · have heq := Result.ok.inj h
    rw [← heq]
    change out.val.concat b = out.val ++ [b]
    exact List.concat_eq_append
  · cases h

theorem nextPublic_success (m : Result (Status × ByteVec))
    (k : ByteVec → Result Output) (out' : ByteVec)
    (h : nextPublic m k = ok (.Ok out')) :
    ∃ out, m = ok (.Ok (), out) ∧ k out = ok (.Ok out') := by
  cases m with
  | fail e => simp [nextPublic] at h
  | div => simp [nextPublic] at h
  | ok r =>
    rcases r with ⟨status, out⟩
    cases status with
    | Err e =>
      simp [nextPublic, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok u =>
      cases u
      exact ⟨out, rfl, by simpa [nextPublic,
        core.result.Result.Insts.CoreOpsTry.branch] using h⟩

theorem program_success (ss : List Step) (out out' : ByteVec)
    (h : program ss out = ok (.Ok out')) :
    canonical (ss.flatMap stepWords) ∧
      out'.val = out.val ++ ss.flatMap stepBytes := by
  induction ss generalizing out with
  | nil =>
    have heq : out = out' := core.result.Result.Ok.inj (Result.ok.inj h)
    subst out'
    simp [canonical]
  | cons s ss ih =>
    cases s with
    | byte b =>
      obtain ⟨out1, hp, hr⟩ := bind_success _ _ _ h
      have hb := push_success out out1 b hp
      have hi := ih out1 hr
      simpa only [List.flatMap_cons, stepWords, stepBytes, List.nil_append,
        hb, List.append_assoc] using hi
    | index n =>
      obtain ⟨out1, he, hr⟩ := bind_success _ _ _ h
      have hb := extend_success out out1
        (Array.to_slice (core.num.U64.to_le_bytes n)) he
      have hi := ih out1 hr
      change out1.val = out.val ++ (core.num.U64.to_le_bytes n).val at hb
      simpa only [List.flatMap_cons, stepWords, stepBytes, List.nil_append,
        hb, List.append_assoc] using hi
    | words s =>
      obtain ⟨out1, hf, hr⟩ := nextPublic_success _ _ _ h
      have hf := fields_success out out1 s hf
      have hi := ih out1 hr
      constructor
      · intro x hx
        simp only [List.flatMap_cons, stepWords, List.mem_append] at hx
        exact hx.elim (hf.1 x) (hi.1 x)
      · simpa only [List.flatMap_cons, stepBytes, hf.2, List.append_assoc] using hi.2
    | frontier f =>
      obtain ⟨out1, hf, hr⟩ := nextPublic_success _ _ _ h
      have hf := frontier_success out out1 f hf
      have hi := ih out1 hr
      constructor
      · intro x hx
        simp only [List.flatMap_cons, stepWords, List.mem_append] at hx
        exact hx.elim (hf.1 x) (hi.1 x)
      · simpa only [List.flatMap_cons, stepBytes, hf.2, List.append_assoc] using hi.2

def single (x : Field) : Slice Field := Array.to_slice (Array.make 1#usize [x])

def tailSteps (t : Transition) : List Step :=
  [.index t.live_snapshot.next_pair_index,
   .frontier t.live_snapshot.frontier,
   .words (Array.to_slice t.candidate_afterstate.next_root),
   .frontier t.candidate_afterstate.next_frontier]

def sourceSteps : Public → List Step
  | .Transfer p t =>
    [.byte 0#u8, .words (Array.to_slice p.anchor_root),
     .words (Array.to_slice p.nullifier), .words (single p.asset_id),
     .byte 1#u8, .words (Array.to_slice p.recipient_commitment),
     .words (Array.to_slice p.change_commitment), .byte 0#u8] ++ tailSteps t
  | .Withdrawal p t =>
    [.byte 1#u8, .words (Array.to_slice p.anchor_root),
     .words (Array.to_slice p.nullifier), .words (single p.asset_id),
     .byte 0#u8, .words (Array.to_slice p.change_commitment),
     .byte 1#u8, .words (single p.amount)] ++ tailSteps t

theorem source_eq_program (p : Public) :
    r0.Public.public_bytes p = program (sourceSteps p) (alloc.vec.Vec.new Std.U8) := by
  cases p <;> rfl

/-- Actual generated entry-point success determines all bytes and proves every
serialized field word canonical. There is no capacity/allocator premise. -/
theorem source_success (p : Public) (out : ByteVec)
    (h : r0.Public.public_bytes p = ok (.Ok out)) :
    canonical ((sourceSteps p).flatMap stepWords) ∧
      out.val = (sourceSteps p).flatMap stepBytes := by
  rw [source_eq_program] at h
  have hs := program_success _ _ out h
  simpa only [alloc.vec.Vec.new, List.nil_append] using hs

#print axioms bind_success
#print axioms push_success
#print axioms nextPublic_success
#print axioms program_success
#print axioms source_eq_program
#print axioms source_success

end AspisR1PublicSerializer.Whole431
