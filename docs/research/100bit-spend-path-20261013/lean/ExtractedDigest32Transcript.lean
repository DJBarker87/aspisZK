import AspisR1PublicPreparation.Funs

/-! Actual emitted constructor and validated step. These equations retain the
Digest32 dictionary and ordered Result binds. They are not a Rust/syscall effect
trace, and do not establish that the full verifier caller executes all33 rows. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.TranscriptStep
open r1_wire

abbrev Bytes32 := Array U8 32#usize

def initParts (bytes : Slice U8) (root : Bytes32) (length : U32) : Slice (Slice U8) :=
  Array.to_slice (Array.make 5#usize [DOMAIN,
    Array.to_slice (Array.make 1#usize [0#u8]),
    Array.to_slice (core.num.U32.to_le_bytes length), bytes, Array.to_slice root])

def absorbParts (state : Bytes32) (tag : U8) (framed : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8, tag]), framed])

def readParts (absorbed : Bytes32) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [Array.to_slice absorbed,
    Array.to_slice (Array.make 1#usize [tag])])

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem new_of_length {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (bytes : Slice U8) (root : Bytes32) (length : U32)
    (hlen : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len bytes) = ok (.Ok length)) :
    SemanticTranscript.new D hash bytes root =
      (do let state ← D.digest hash (initParts bytes root length)
          ok (.Ok { state, hash, next_row := 0#u8 })) := by
  simp only [SemanticTranscript.new, hlen, core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch, lift, bind_tc_ok, initParts]

theorem new_success {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (bytes : Slice U8) (root : Bytes32) (out : SemanticTranscript H)
    (h : SemanticTranscript.new D hash bytes root = ok (.Ok out)) :
    ∃ length state,
      core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
        (Slice.len bytes) = ok (.Ok length) ∧
      D.digest hash (initParts bytes root length) = ok state ∧
      out = { state, hash, next_row := 0#u8 } := by
  have hcopy := h
  unfold SemanticTranscript.new at h
  obtain ⟨r, hr, h⟩ := bind_success
    (core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes)) _ _ h
  cases r with
  | Ok length =>
    rw [new_of_length D hash bytes root length hr] at hcopy
    obtain ⟨state, hs, hout⟩ := bind_success _ _ _ hcopy
    exact ⟨length, state, hr, hs, (core.result.Result.Ok.inj (Result.ok.inj hout)).symm⟩
  | Err e =>
    simp only [core.result.Result.map_err,
      SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h

theorem wrong_row {H : Type} (D : aspis_core.Digest32 H)
    (self : SemanticTranscript H) (row : U8) (framed : Slice U8)
    (hrow : row ≠ self.next_row) :
    SemanticTranscript.sample_block_validated D self row framed =
      ok (.Err (.RowOrder self.next_row row), self) := by
  simp [SemanticTranscript.sample_block_validated, hrow]

/-- Exact three-call order; both read calls use the absorbed state. -/
theorem step_of_add {H : Type} (D : aspis_core.Digest32 H)
    (self : SemanticTranscript H) (row tag next : U8) (framed : Slice U8)
    (hrow : row = self.next_row) (htag : 160#u8 + row = ok tag)
    (hnext : self.next_row + 1#u8 = ok next) :
    SemanticTranscript.sample_block_validated D self row framed =
      (do let absorbed ← D.digest self.hash (absorbParts self.state tag framed)
          let block ← D.digest self.hash (readParts absorbed 1#u8)
          let state ← D.digest self.hash (readParts absorbed 2#u8)
          ok (.Ok block, { self with state, next_row := next })) := by
  have hguard : (row != self.next_row) = false := by simp [hrow]
  simp only [SemanticTranscript.sample_block_validated, hguard,
    Bool.false_eq_true, if_false, lift, bind_tc_ok, htag, hnext,
    absorbParts, readParts]

/-- On admitted semantic rows, success fixes exact inputs, outputs and carry.
Arithmetic and dictionary success are consequences, not extra premises. -/
theorem step_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (row : U8) (framed : Slice U8)
    (block : Bytes32) (hadmit : row.val ≤ 26)
    (h : SemanticTranscript.sample_block_validated D self row framed =
      ok (.Ok block, after)) :
    row = self.next_row ∧ ∃ tag next absorbed state,
      tag.val = 160 + row.val ∧ next.val = row.val + 1 ∧
      D.digest self.hash (absorbParts self.state tag framed) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      after = { self with state, next_row := next } := by
  have hrow : row = self.next_row := by
    by_contra hn
    rw [wrong_row D self row framed hn] at h
    cases h
  obtain ⟨tag, htag, htagval⟩ := WP.spec_imp_exists
    (U8.add_spec (x := 160#u8) (y := row) (by scalar_tac))
  obtain ⟨next, hnext, hnextval⟩ := WP.spec_imp_exists
    (U8.add_spec (x := self.next_row) (y := 1#u8)
      (by rw [← hrow]; scalar_tac))
  rw [step_of_add D self row tag next framed hrow htag hnext] at h
  obtain ⟨absorbed, ha, h⟩ := bind_success _ _ _ h
  obtain ⟨b, hb, h⟩ := bind_success _ _ _ h
  obtain ⟨state, hs, h⟩ := bind_success _ _ _ h
  have pairEq := Result.ok.inj h
  have blockEq := core.result.Result.Ok.inj (congrArg Prod.fst pairEq)
  have afterEq := congrArg Prod.snd pairEq
  refine ⟨hrow, tag, next, absorbed, state, ?_, ?_, ha, ?_, hs, afterEq.symm⟩
  · simpa using htagval
  · simpa [← hrow] using hnextval
  · simpa only [blockEq] using hb

#print axioms new_of_length
#print axioms new_success
#print axioms wrong_row
#print axioms step_of_add
#print axioms step_success
end AspisR1PublicPreparation.TranscriptStep
