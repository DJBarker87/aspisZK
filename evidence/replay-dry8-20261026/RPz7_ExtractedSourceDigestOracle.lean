import RPz7_ExtractedSourceDigestAddresses
/-! Proof-only construction of a functional oracle for the exact source-call
grammar. D may depend on slice grouping: the inverse lemma establishes equality
of the actual grouped input, before invoking D's functional equality. No SHA,
distribution, table-recovery or custody premise appears here. -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceDigestOracle
open r1_wire TranscriptStep SourceDigestAddresses
open FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
attribute [local instance] Classical.propDecidable

/-- One fixed actual initializer, and the exact two subsequent source layouts.
This is input syntax, not a replacement transcript/state/sampler model. -/
inductive Input where
  | initial
  | absorb (state : Bytes32) (tag : U8) (framed : Slice U8)
  | read (state : Bytes32) (tag : U8)

def parts (pubInput : Slice U8) (root : Bytes32) (length : U32) :
    Input → Slice (Slice U8)
  | .initial => initParts pubInput root length
  | .absorb state tag framed => absorbParts state tag framed
  | .read state tag => readParts state tag

private theorem prefix_split {α : Type} (n : Nat) (a b c d : List α)
    (ha : a.length = n) (hb : b.length = n) (h : a ++ c = b ++ d) :
    a = b ∧ c = d := by
  have hta : (a ++ c).take n = a := by
    rw [List.take_append_of_le_length (by omega), ← ha, List.take_length]
  have htb : (b ++ d).take n = b := by
    rw [List.take_append_of_le_length (by omega), ← hb, List.take_length]
  have he : a = b := hta.symm.trans ((congrArg (List.take n) h).trans htb)
  subst b
  exact ⟨rfl, List.append_cancel_left h⟩

private theorem raw_slice_injective (a b : Slice U8) (h : rawBytes a = rawBytes b) : a = b := by
  apply Subtype.ext
  have he := congrArg (List.map encodeByte) h
  simpa [rawBytes, List.map_map, Function.comp_def, word_roundtrip] using he

private theorem raw_array_injective (a b : Bytes32)
    (h : bytes (decodeState a) = bytes (decodeState b)) : a = b := by
  apply Subtype.ext
  rw [state_bytes, state_bytes] at h
  have he := congrArg (List.map encodeByte) h
  simpa [List.map_map, Function.comp_def, word_roundtrip] using he

private theorem byte_injective (a b : U8) (h : decodeByte a = decodeByte b) : a = b := by
  apply UScalar.eq_of_val_eq
  exact congrArg Fin.val h

theorem absorb_parts_of_flat (a b : Bytes32) (ta tb : U8) (fa fb : Slice U8)
    (h : flatten (absorbParts a ta fa) = flatten (absorbParts b tb fb)) :
    absorbParts a ta fa = absorbParts b tb fb := by
  rw [flatten_absorb, flatten_absorb] at h
  have he := prefix_split 32 (bytes (decodeState a)) (bytes (decodeState b))
    ([0, decodeByte ta] ++ rawBytes fa) ([0, decodeByte tb] ++ rawBytes fb)
    (bytes_length _) (bytes_length _) (by simpa only [List.append_assoc] using h)
  have hs := raw_array_injective a b he.1
  have ht := (List.cons.inj ((List.cons.inj he.2).2)).1
  have hf := (List.cons.inj ((List.cons.inj he.2).2)).2
  have htag := byte_injective ta tb ht
  have hframe := raw_slice_injective fa fb hf
  cases hs; cases htag; cases hframe
  rfl

theorem read_parts_of_flat (a b : Bytes32) (ta tb : U8)
    (h : flatten (readParts a ta) = flatten (readParts b tb)) :
    readParts a ta = readParts b tb := by
  rw [flatten_read, flatten_read] at h
  obtain ⟨hs, ht⟩ := prefix_split 32 (bytes (decodeState a)) (bytes (decodeState b))
    [decodeByte ta] [decodeByte tb] (bytes_length _) (bytes_length _) h
  have hs := raw_array_injective a b hs
  have htag := byte_injective ta tb (List.cons.inj ht).1
  cases hs; cases htag
  rfl

theorem absorb_length (s : Bytes32) (tag : U8) (framed : Slice U8) :
    (flatten (absorbParts s tag framed)).length = 34 + (rawBytes framed).length := by
  simp [flatten_absorb, bytes_length]
  omega

theorem read_length (s : Bytes32) (tag : U8) :
    (flatten (readParts s tag)).length = 33 := by
  simp [flatten_read, bytes_length]

theorem init_length (pubInput : Slice U8) (root : Bytes32) (length : U32) :
    (flatten (initParts pubInput root length)).length = 75 + (rawBytes pubInput).length := by
  simp [flatten_init, AspisR1.PublicInitFrame.domain,
    AspisR1.PublicInitFrame.lengthBytes_length, bytes_length] <;> omega

theorem absorb_marker (s : Bytes32) (tag : U8) (framed : Slice U8) :
    (flatten (absorbParts s tag framed))[32]? = some (0 : AspisV8R19.DuplexFrames.Byte) := by
  simp [flatten_absorb, List.append_assoc, List.getElem?_append, bytes_length]

theorem init_marker (pubInput : Slice U8) (root : Bytes32) (length : U32) :
    (flatten (initParts pubInput root length))[32]? = some (84 : AspisV8R19.DuplexFrames.Byte) := by
  rw [flatten_init]
  rfl

private theorem init_ne_absorb (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (s : Bytes32) (tag : U8) (framed : Slice U8) :
    flatten (initParts pubInput root length) ≠ flatten (absorbParts s tag framed) := by
  intro h
  have hm := congrArg (fun bs : Bytes => bs[32]?) h
  rw [init_marker, absorb_marker] at hm
  have hv := congrArg Fin.val (Option.some.inj hm)
  norm_num at hv

private theorem init_ne_read (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (s : Bytes32) (tag : U8) :
    flatten (initParts pubInput root length) ≠ flatten (readParts s tag) := by
  intro h
  have hl := congrArg List.length h
  rw [init_length, read_length] at hl
  omega

private theorem absorb_ne_read (s t : Bytes32) (tag readTag : U8) (framed : Slice U8) :
    flatten (absorbParts s tag framed) ≠ flatten (readParts t readTag) := by
  intro h
  have hl := congrArg List.length h
  rw [absorb_length, read_length] at hl
  omega

/-- Address equality recovers exact source slice grouping, not merely bytes.
The initializer is fixed once; no arbitrary initializer inversion is assumed. -/
theorem parts_of_flat (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (a b : Input) (h : flatten (parts pubInput root length a) =
      flatten (parts pubInput root length b)) :
    parts pubInput root length a = parts pubInput root length b := by
  cases a with
  | initial =>
    cases b with
    | initial => rfl
    | absorb s tag framed => exact (init_ne_absorb pubInput root length s tag framed h).elim
    | read s tag => exact (init_ne_read pubInput root length s tag h).elim
  | absorb s tag framed =>
    cases b with
    | initial => exact (init_ne_absorb pubInput root length s tag framed h.symm).elim
    | absorb t other otherFrame => exact absorb_parts_of_flat s t tag other framed otherFrame h
    | read t readTag => exact (absorb_ne_read s t tag readTag framed h).elim
  | read s tag =>
    cases b with
    | initial => exact (init_ne_read pubInput root length s tag h.symm).elim
    | absorb t absorbTag framed => exact (absorb_ne_read t s absorbTag tag framed h.symm).elim
    | read t other => exact read_parts_of_flat s t tag other h

def answer {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (input : Slice (Slice U8)) : State :=
  match D.digest hash input with
  | .ok output => decodeState output
  | .fail _ => 0
  | .div => 0

/-- A total function on the same finite Addr L space, constructed from the
actual dictionary and canonical source grouping. Defaults are unreachable for
the successfully reached calls used by oracle_at. No distribution is claimed. -/
def oracle {Hash : Type} {L : Nat} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : Slice U8) (root : Bytes32) (length : U32) (address : Addr L) : State :=
  if h : ∃ input : Input, flatten (parts pubInput root length input) = address.toBytes then
    answer D hash (parts pubInput root length (Classical.choose h))
  else 0

theorem oracle_at {Hash : Type} {L : Nat} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : Slice U8) (root : Bytes32) (length : U32) (input : Input)
    (address : Addr L) (output : Bytes32)
    (ha : flatten (parts pubInput root length input) = address.toBytes)
    (hd : D.digest hash (parts pubInput root length input) = ok output) :
    decodeState output = oracle D hash pubInput root length address := by
  have hex : ∃ i : Input, flatten (parts pubInput root length i) = address.toBytes := ⟨input, ha⟩
  have hg := Classical.choose_spec hex
  have he := parts_of_flat pubInput root length (Classical.choose hex) input (hg.trans ha.symm)
  unfold oracle
  rw [dif_pos hex, he]
  simp only [answer, hd]

/-- The source's same carried hash is derived from the actual Call trace. -/
theorem trace_hashes {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    {before after : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs) :
    after.hash = before.hash ∧ ∀ c ∈ cs, c.before.hash = before.hash := by
  induction run with
  | nil self => exact ⟨rfl, by simp⟩
  | cons c tail ih =>
    have hc : c.after.hash = c.before.hash := by rw [c.carried]
    refine ⟨ih.1.trans hc, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · cases he; rfl
    · exact (ih.2 d he).trans hc

/-- No DigestAt premise: the constructed source oracle interprets every
actual successful row call at its exact grouped input. -/
theorem call_functional {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash}
    {pre : Prefix} (p : Params M Cv L) (c : SourceFull25.Call D pre)
    (hash : Hash) (hhash : c.before.hash = hash)
    (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (hD : (rawBytes c.record.framed).length ≤ p.D) :
    let H := oracle D hash pubInput root length
    decodeState c.absorbed = H (absorbA p (decodeState c.before.state)
      (decodeByte c.tag) (rawBytes c.record.framed) hD) ∧
    decodeState c.block = H (squeezeA p (decodeState c.absorbed)) ∧
    decodeState c.after.state = H (advanceA p (decodeState c.absorbed)) := by
  have ha := c.absorb
  have h1 := c.read1
  have h2 := c.read2
  rw [hhash] at ha h1 h2
  refine ⟨oracle_at D hash pubInput root length (.absorb _ _ _) _ c.absorbed
    (absorb_address p _ _ _ hD) ha,
    oracle_at D hash pubInput root length (.read _ 1#u8) _ c.block
      (SourceDigestAddresses.squeeze_address p _) h1, ?_⟩
  rw [c.carried]
  exact oracle_at D hash pubInput root length (.read _ 2#u8) _ c.state
    (SourceDigestAddresses.advance_address p _) h2

theorem trace_functional {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash}
    {pre : Prefix} (p : Params M Cv L)
    {before after : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (hD : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D) :
    let H := oracle D before.hash pubInput root length
    ∀ (c : SourceFull25.Call D pre) (hc : c ∈ cs),
      decodeState c.absorbed = H (absorbA p (decodeState c.before.state)
        (decodeByte c.tag) (rawBytes c.record.framed) (hD c hc)) ∧
      decodeState c.block = H (squeezeA p (decodeState c.absorbed)) ∧
      decodeState c.after.state = H (advanceA p (decodeState c.absorbed)) := by
  dsimp only
  intro c hc
  exact call_functional p c before.hash ((trace_hashes run).2 c hc)
    pubInput root length (hD c hc)

/-- Actual public helper success fixes one initializer and the same generic
hash. Its functional oracle equation is a conclusion, not a new assumption. -/
theorem public_oracle {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : Bytes32) (out : SemanticTranscript Hash)
    (h : r1_semantic.public_transcript D pubInput hash root = ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (length : U32),
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput = ok (.Ok encoded) ∧
      out.hash = hash ∧
      ∀ {L : Nat} (hL : 75 + (rawBytes (alloc.vec.Vec.deref encoded)).length ≤ L),
        decodeState out.state = oracle D hash (alloc.vec.Vec.deref encoded) root length
          (AspisR1.PublicInitFrame.addr (rawBytes (alloc.vec.Vec.deref encoded)) hL
            (decodeState root)) := by
  obtain ⟨encoded, length, state, he, hd, hout, haddr⟩ :=
    public_init_address D hash pubInput root out h
  refine ⟨encoded, length, he, by rw [hout], ?_⟩
  intro L hL
  rw [hout]
  exact oracle_at D hash (alloc.vec.Vec.deref encoded) root length .initial _ state
    (haddr hL) hd

#print axioms absorb_parts_of_flat
#print axioms read_parts_of_flat
#print axioms absorb_length
#print axioms read_length
#print axioms init_length
#print axioms absorb_marker
#print axioms init_marker
#print axioms parts_of_flat
#print axioms answer
#print axioms oracle
#print axioms oracle_at
#print axioms trace_hashes
#print axioms call_functional
#print axioms trace_functional
#print axioms public_oracle
end AspisR1PublicPreparation.SourceDigestOracle
end
