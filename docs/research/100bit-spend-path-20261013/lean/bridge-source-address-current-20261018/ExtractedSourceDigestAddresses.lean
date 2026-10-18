import ExtractedSourceFull25Frames
import R1PublicInitFrame
import AspisV8R19.SqueezeOracleBridge

/-! Exact byte addresses of the current source dictionary calls.  The separate
finite `DigestAt` interpretation premise is functional correspondence only; it
does not assert a random-oracle law, table recovery, or commitment custody. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceDigestAddresses
open r1_wire TranscriptStep
open FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def rawBytes (s : Slice U8) : Bytes := s.val.map decodeByte

@[simp] theorem decode_zero : decodeByte 0#u8 = (0 : AspisV8R19.DuplexFrames.Byte) := by
  apply Fin.ext; rfl

theorem state_bytes (s : Bytes32) : bytes (decodeState s) = s.val.map decodeByte := by
  have h := congrArg (fun a : Bytes32 => a.val.map decodeByte) (array_roundtrip s)
  simpa [encodeState, List.map_map, Function.comp_def, byte_roundtrip] using h

theorem flatten_absorb (s : Bytes32) (tag : U8) (framed : Slice U8) :
    flatten (absorbParts s tag framed) =
      bytes (decodeState s) ++ [0, decodeByte tag] ++ rawBytes framed := by
  simp [flatten, absorbParts, Array.to_slice, Array.make, rawBytes, state_bytes,
    List.map_append]

theorem flatten_read (s : Bytes32) (tag : U8) :
    flatten (readParts s tag) = bytes (decodeState s) ++ [decodeByte tag] := by
  simp [flatten, readParts, Array.to_slice, Array.make, state_bytes]

theorem absorb_address {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (s : Bytes32) (tag : U8) (framed : Slice U8)
    (hD : (rawBytes framed).length ≤ p.D) :
    flatten (absorbParts s tag framed) =
      (absorbA p (decodeState s) (decodeByte tag) (rawBytes framed) hD).toBytes := by
  rw [absorbA, Addr.toBytes_ofBytes, flatten_absorb]
  rfl

theorem squeeze_address {M Cv : Type} {L : Nat} (p : Params M Cv L) (s : Bytes32) :
    flatten (readParts s 1#u8) = (squeezeA p (decodeState s)).toBytes := by
  rw [squeezeA, Addr.toBytes_ofBytes, flatten_read]
  rfl

theorem advance_address {M Cv : Type} {L : Nat} (p : Params M Cv L) (s : Bytes32) :
    flatten (readParts s 2#u8) = (advanceA p (decodeState s)).toBytes := by
  rw [advanceA, Addr.toBytes_ofBytes, flatten_read]
  rfl

theorem length_bytes (n : U32) :
    (core.num.U32.to_le_bytes n).val.map decodeByte =
      AspisR1.PublicInitFrame.lengthBytes n.val := by
  change (core.num.U32.to_le_bytes n).val.map (fun b => b.bv.toFin) = _
  apply List.ext_getElem
  · simp [core.num.U32.to_le_bytes, AspisR1.PublicInitFrame.lengthBytes]
  · intro i hi hj
    have hi4 : i < 4 := by
      have hl : (core.num.U32.to_le_bytes n).val.length = 4 :=
        (core.num.U32.to_le_bytes n).property
      simpa only [List.length_map, hl] using hi
    have cases4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases4 with rfl | rfl | rfl | rfl <;>
      apply Fin.ext <;>
      simp [core.num.U32.to_le_bytes, AspisR1.PublicInitFrame.lengthBytes,
        BitVec.toLEBytes, BitVec.toNat_setWidth,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega

theorem domain_bytes : rawBytes DOMAIN = AspisR1.PublicInitFrame.domain := by
  unfold rawBytes DOMAIN AspisR1.PublicInitFrame.domain
  rfl

theorem flatten_init (pubInput : Slice U8) (root : Bytes32) (length : U32) :
    flatten (initParts pubInput root length) =
      AspisR1.PublicInitFrame.domain ++ [0] ++
        AspisR1.PublicInitFrame.lengthBytes length.val ++ rawBytes pubInput ++
        bytes (decodeState root) := by
  simp [flatten, initParts, Array.to_slice, Array.make, ← domain_bytes,
    rawBytes, length_bytes, state_bytes, List.append_assoc]

theorem init_address {L : Nat} (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (hlen : length.val = (rawBytes pubInput).length)
    (hL : 75 + (rawBytes pubInput).length ≤ L) :
    flatten (initParts pubInput root length) =
      (AspisR1.PublicInitFrame.addr (rawBytes pubInput) hL (decodeState root)).toBytes := by
  rw [AspisR1.PublicInitFrame.addr_bytes, flatten_init, hlen]

theorem successful_length (pubInput : Slice U8) (length : U32)
    (h : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len pubInput) = ok (.Ok length)) :
    length.val = (rawBytes pubInput).length := by
  have hs := core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from.step_spec
    (Slice.len pubInput)
  simp only [h, WP.spec_ok] at hs
  have hb : (Slice.len pubInput).val ≤ U32.max := by
    by_contra hn
    have he := hs.2 (by omega)
    cases he
  obtain ⟨actual, he, hv⟩ := hs.1 hb
  cases he
  simpa [rawBytes, Slice.len] using hv

/-- The source constructor supplies its own exact public length and digest
input.  The address bound is a size premise, not a serializer/custody premise. -/
theorem new_address {H : Type} {L : Nat} (D : aspis_core.Digest32 H) (hash : H)
    (pubInput : Slice U8) (root : Bytes32) (out : SemanticTranscript H)
    (hL : 75 + (rawBytes pubInput).length ≤ L)
    (h : SemanticTranscript.new D hash pubInput root = ok (.Ok out)) :
    ∃ length state,
      D.digest hash (initParts pubInput root length) = ok state ∧
      flatten (initParts pubInput root length) =
        (AspisR1.PublicInitFrame.addr (rawBytes pubInput) hL (decodeState root)).toBytes ∧
      out = { state, hash, next_row := 0#u8 } := by
  obtain ⟨length, state, hlen, hd, hout⟩ := new_success D hash pubInput root out h
  exact ⟨length, state, hd, init_address pubInput root length
    (successful_length pubInput length hlen) hL, hout⟩

/-- Actual public helper success reaches the constructor on the actual vector
returned by the same serializer. No independent byte/constructor premise. -/
theorem public_new {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : Bytes32) (out : SemanticTranscript H)
    (h : r1_semantic.public_transcript D pubInput hash root = ok (.Ok out)) :
    ∃ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput = ok (.Ok encoded) ∧
      SemanticTranscript.new D hash (alloc.vec.Vec.deref encoded) root = ok (.Ok out) := by
  unfold r1_semantic.public_transcript at h
  obtain ⟨encoded, he, h⟩ := bind_success _ _ _ h
  cases encoded with
  | Ok encoded =>
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      lift, bind_tc_ok] at h
    exact ⟨encoded, he, h⟩
  | Err error =>
    simp only [core.result.Result.map_err,
      r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch, lift, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h

/-- The full initializer witness follows from actual helper success. Public
bytes and the constructor length are existential outputs of those actual calls. -/
theorem public_init_address {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : Bytes32) (out : SemanticTranscript H)
    (h : r1_semantic.public_transcript D pubInput hash root = ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (length : U32) (state : Bytes32),
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) ∧
      D.digest hash (initParts (alloc.vec.Vec.deref encoded) root length) = ok state ∧
      out = { state, hash, next_row := 0#u8 } ∧
      ∀ {L : Nat} (hL : 75 + (rawBytes (alloc.vec.Vec.deref encoded)).length ≤ L),
        flatten (initParts (alloc.vec.Vec.deref encoded) root length) =
          (AspisR1.PublicInitFrame.addr (rawBytes (alloc.vec.Vec.deref encoded)) hL
            (decodeState root)).toBytes := by
  obtain ⟨encoded, he, hn⟩ := public_new D hash pubInput root out h
  obtain ⟨length, state, hlen, hd, hout⟩ :=
    new_success D hash (alloc.vec.Vec.deref encoded) root out hn
  refine ⟨encoded, length, state, he, hd, hout, ?_⟩
  intro L hL
  exact init_address _ root length (successful_length _ length hlen) hL

/-- A finite functional interpretation at one exact source call/address.
This premise is deliberately separate from table/read/collision/custody facts. -/
def DigestAt {H : Type} {L : Nat} (D : aspis_core.Digest32 H) (hash : H)
    (oracle : Addr L → State) (parts : Slice (Slice U8)) (address : Addr L) : Prop :=
  ∀ result, D.digest hash parts = ok result → decodeState result = oracle address

theorem call_addresses {H M Cv : Type} {L : Nat} {D : aspis_core.Digest32 H}
    {pre : Prefix} (p : Params M Cv L) (c : SourceFull25.Call D pre)
    (hD : (rawBytes c.record.framed).length ≤ p.D) :
    flatten (absorbParts c.before.state c.tag c.record.framed) =
      (absorbA p (decodeState c.before.state) (decodeByte c.tag)
        (rawBytes c.record.framed) hD).toBytes ∧
    flatten (readParts c.absorbed 1#u8) = (squeezeA p (decodeState c.absorbed)).toBytes ∧
    flatten (readParts c.absorbed 2#u8) = (advanceA p (decodeState c.absorbed)).toBytes ∧
    (decodeByte c.tag).val = 160 + c.row.val := by
  exact ⟨absorb_address p _ _ _ hD, squeeze_address p _, advance_address p _,
    by simpa only [decodeByte, c.record_row] using c.tag_code⟩

/-- Actual source success supplies all three outputs.  Only interpretation at
these three concrete calls is supplied; successor state is recovered from the
same Call's source carry equation, rather than assumed independently. -/
theorem call_functional {H M Cv : Type} {L : Nat} {D : aspis_core.Digest32 H}
    {pre : Prefix} (p : Params M Cv L) (c : SourceFull25.Call D pre)
    (hD : (rawBytes c.record.framed).length ≤ p.D) (oracle : Addr L → State)
    (ha : DigestAt D c.before.hash oracle
      (absorbParts c.before.state c.tag c.record.framed)
      (absorbA p (decodeState c.before.state) (decodeByte c.tag)
        (rawBytes c.record.framed) hD))
    (h1 : DigestAt D c.before.hash oracle (readParts c.absorbed 1#u8)
      (squeezeA p (decodeState c.absorbed)))
    (h2 : DigestAt D c.before.hash oracle (readParts c.absorbed 2#u8)
      (advanceA p (decodeState c.absorbed))) :
    decodeState c.absorbed = oracle (absorbA p (decodeState c.before.state)
      (decodeByte c.tag) (rawBytes c.record.framed) hD) ∧
    decodeState c.block = oracle (squeezeA p (decodeState c.absorbed)) ∧
    decodeState c.after.state = oracle (advanceA p (decodeState c.absorbed)) := by
  refine ⟨ha _ c.absorb, h1 _ c.read1, ?_⟩
  rw [c.carried]
  exact h2 _ c.read2

#print axioms rawBytes
#print axioms decode_zero
#print axioms state_bytes
#print axioms flatten_absorb
#print axioms flatten_read
#print axioms absorb_address
#print axioms squeeze_address
#print axioms advance_address
#print axioms length_bytes
#print axioms domain_bytes
#print axioms flatten_init
#print axioms init_address
#print axioms successful_length
#print axioms new_address
#print axioms public_new
#print axioms public_init_address
#print axioms DigestAt
#print axioms call_addresses
#print axioms call_functional
end AspisR1PublicPreparation.SourceDigestAddresses
