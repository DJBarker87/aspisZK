import ActualDecodeKStrictQM31Parser

/-! Total execution of the actual extracted indexed value decoder, including
all sixteen reads, under explicit payload and range premises. Invalid field
bytes are ordinary Rust errors; no successful decoding is assumed. -/
set_option autoImplicit false
namespace AspisR1.R22DecodeValueTotal
open Aeneas Aeneas.Std Result
abbrev Record := AspisR1DecodeKFullV10.r1_wire.ValidatedRecord
abbrev Q := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev E := AspisR1DecodeKFullV10.r1_wire.Error

private theorem add_total (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, (a + b : Result Usize) = .ok c ∧ c.val = a.val + b.val := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq] using h

private theorem mul_total (a b : Usize) (h : a.val * b.val ≤ Usize.max) :
    ∃ c : Usize, (a * b : Result Usize) = .ok c ∧ c.val = a.val * b.val := by
  apply WP.spec_imp_exists
  apply UScalar.mul_spec
  simpa only [UScalar.max_USize_eq] using h

private theorem read_offset (bytes : Slice U8) (start delta : Usize)
    (h : start.val + 16 ≤ bytes.val.length) (hk : delta.val < 16) :
    ∃ p : Usize, ∃ b : U8,
      (start + delta : Result Usize) = .ok p ∧ Slice.index_usize bytes p = .ok b := by
  have hlen : bytes.val.length ≤ Usize.max := bytes.property
  obtain ⟨p, hp, hv⟩ := add_total start delta (by omega)
  obtain ⟨b, hb, _⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes p
    (by change p.val < bytes.val.length; omega))
  exact ⟨p, b, hp, hb⟩

/-- Outer checked end and slice guards imply every inner arithmetic bound. -/
theorem size_guards (offset count value limit : Nat)
    (hv : value < count) (hend : 32*offset + 32*count ≤ limit) :
    32*value ≤ limit ∧
    32*offset + 32*value + 16 ≤ limit ∧
    offset + value ≤ limit := by omega

/-- No Aeneas failure, including overflow or bounds failure, for a selected
value. The payload theorem is a framing premise supplied outside this cone. -/
theorem decode_value_total
    (self : Record) (byteOffset value offsetValues : Usize) (bytes : Slice U8)
    (hpayload : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload self = .ok bytes)
    (hmul : value.val * 32 ≤ Usize.max)
    (hreads : byteOffset.val + value.val*32 + 16 ≤ bytes.val.length)
    (hoffset : offsetValues.val + value.val ≤ Usize.max) :
    ∃ out : core.result.Result Q E,
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
        self byteOffset value offsetValues = .ok out := by
  obtain ⟨stride, hstride, hvstride⟩ := mul_total value 32#usize (by simpa using hmul)
  change stride.val = value.val * 32 at hvstride
  have hlen : bytes.val.length ≤ Usize.max := bytes.property
  obtain ⟨start, hstart, hvstart⟩ := add_total byteOffset stride (by omega)
  have hstart16 : start.val + 16 ≤ bytes.val.length := by omega
  obtain ⟨b0, hb0, _⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec bytes start (by change start.val < bytes.val.length; omega))
  obtain ⟨p1, b1, hp1, hb1⟩ := read_offset bytes start 1#usize hstart16 (by decide)
  obtain ⟨p2, b2, hp2, hb2⟩ := read_offset bytes start 2#usize hstart16 (by decide)
  obtain ⟨p3, b3, hp3, hb3⟩ := read_offset bytes start 3#usize hstart16 (by decide)
  obtain ⟨p4, b4, hp4, hb4⟩ := read_offset bytes start 4#usize hstart16 (by decide)
  obtain ⟨p5, b5, hp5, hb5⟩ := read_offset bytes start 5#usize hstart16 (by decide)
  obtain ⟨p6, b6, hp6, hb6⟩ := read_offset bytes start 6#usize hstart16 (by decide)
  obtain ⟨p7, b7, hp7, hb7⟩ := read_offset bytes start 7#usize hstart16 (by decide)
  obtain ⟨p8, b8, hp8, hb8⟩ := read_offset bytes start 8#usize hstart16 (by decide)
  obtain ⟨p9, b9, hp9, hb9⟩ := read_offset bytes start 9#usize hstart16 (by decide)
  obtain ⟨p10, b10, hp10, hb10⟩ := read_offset bytes start 10#usize hstart16 (by decide)
  obtain ⟨p11, b11, hp11, hb11⟩ := read_offset bytes start 11#usize hstart16 (by decide)
  obtain ⟨p12, b12, hp12, hb12⟩ := read_offset bytes start 12#usize hstart16 (by decide)
  obtain ⟨p13, b13, hp13, hb13⟩ := read_offset bytes start 13#usize hstart16 (by decide)
  obtain ⟨p14, b14, hp14, hb14⟩ := read_offset bytes start 14#usize hstart16 (by decide)
  obtain ⟨p15, b15, hp15, hb15⟩ := read_offset bytes start 15#usize hstart16 (by decide)
  obtain ⟨finalOffset, hfinal, _⟩ := add_total offsetValues value hoffset
  let arr : Array U8 16#usize := Array.make 16#usize [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15]
  have hparse := ActualDecodeKStrictQM31Parser.source_refines arr
  let parsed := (RetainedFieldByteCodec.decodeQM31LE
    (CandidateParserByteOrder.arrayBytes16 arr)).map ActualDecodeKStrictQM31Parser.limbsToActual
  have hparse' : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes
      (Array.to_slice arr) = .ok parsed := hparse
  unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
  simp only [hstride, hstart, hpayload, hb0, hp1, hb1, hp2, hb2, hp3, hb3, hp4, hb4, hp5, hb5, hp6, hb6, hp7, hb7, hp8, hb8, hp9, hb9, hp10, hb10, hp11, hb11, hp12, hb12, hp13, hb13, hp14, hb14, hp15, hb15, lift, bind_tc_ok]
  change ∃ out, (do
    let o ← AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)
    let i ← offsetValues + value
    AspisR1DecodeKFullV10.core.option.Option.ok_or o (AspisR1DecodeKFullV10.r1_wire.Error.NonCanonical self.row i)) = .ok out
  rw [hparse']
  simp only [bind_tc_ok, hfinal]
  cases parsed <;> exact ⟨_, rfl⟩

#print axioms add_total
#print axioms mul_total
#print axioms read_offset
#print axioms size_guards
#print axioms decode_value_total
end AspisR1.R22DecodeValueTotal
