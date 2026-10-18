import AspisR1DecodeKFullV10.Funs

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result
namespace AspisR1DecodeKFullValueTrace

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev US := Std.UScalar Std.UScalarTy.Usize
abbrev U8 := Std.U8
abbrev Bytes := Slice Std.U8
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error

structure ParserTrace
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset value offsetValues : US) (q : QM) where
  strideValue : US
  payloadStart : US
  finalOffset : US
  payloadData : Bytes
  inputBytes : Bytes
  p1 : US
  p2 : US
  p3 : US
  p4 : US
  p5 : US
  p6 : US
  p7 : US
  p8 : US
  p9 : US
  p10 : US
  p11 : US
  p12 : US
  p13 : US
  p14 : US
  p15 : US
  b0 : U8
  b1 : U8
  b2 : U8
  b3 : U8
  b4 : U8
  b5 : U8
  b6 : U8
  b7 : U8
  b8 : U8
  b9 : U8
  b10 : U8
  b11 : U8
  b12 : U8
  b13 : U8
  b14 : U8
  b15 : U8
  hoffsetMul : value * 32#usize = Result.ok strideValue
  hstart : byteOffset + strideValue = Result.ok payloadStart
  hpayload : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload self = Result.ok payloadData
  hread0 : Slice.index_usize payloadData payloadStart = Result.ok b0
  hp1 : payloadStart + 1#usize = Result.ok p1
  hread1 : Slice.index_usize payloadData p1 = Result.ok b1
  hp2 : payloadStart + 2#usize = Result.ok p2
  hread2 : Slice.index_usize payloadData p2 = Result.ok b2
  hp3 : payloadStart + 3#usize = Result.ok p3
  hread3 : Slice.index_usize payloadData p3 = Result.ok b3
  hp4 : payloadStart + 4#usize = Result.ok p4
  hread4 : Slice.index_usize payloadData p4 = Result.ok b4
  hp5 : payloadStart + 5#usize = Result.ok p5
  hread5 : Slice.index_usize payloadData p5 = Result.ok b5
  hp6 : payloadStart + 6#usize = Result.ok p6
  hread6 : Slice.index_usize payloadData p6 = Result.ok b6
  hp7 : payloadStart + 7#usize = Result.ok p7
  hread7 : Slice.index_usize payloadData p7 = Result.ok b7
  hp8 : payloadStart + 8#usize = Result.ok p8
  hread8 : Slice.index_usize payloadData p8 = Result.ok b8
  hp9 : payloadStart + 9#usize = Result.ok p9
  hread9 : Slice.index_usize payloadData p9 = Result.ok b9
  hp10 : payloadStart + 10#usize = Result.ok p10
  hread10 : Slice.index_usize payloadData p10 = Result.ok b10
  hp11 : payloadStart + 11#usize = Result.ok p11
  hread11 : Slice.index_usize payloadData p11 = Result.ok b11
  hp12 : payloadStart + 12#usize = Result.ok p12
  hread12 : Slice.index_usize payloadData p12 = Result.ok b12
  hp13 : payloadStart + 13#usize = Result.ok p13
  hread13 : Slice.index_usize payloadData p13 = Result.ok b13
  hp14 : payloadStart + 14#usize = Result.ok p14
  hread14 : Slice.index_usize payloadData p14 = Result.ok b14
  hp15 : payloadStart + 15#usize = Result.ok p15
  hread15 : Slice.index_usize payloadData p15 = Result.ok b15
  hinput : lift (Array.to_slice (Array.make 16#usize
    [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15])) = Result.ok inputBytes
  hparse : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes inputBytes = Result.ok (some q)
  hoffsetValues : offsetValues + value = Result.ok finalOffset

private theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = Result.ok y) :
    ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem decode_k_value_success_parser_trace
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset value offsetValues : US) (q : QM)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
      self byteOffset value offsetValues = Result.ok (.Ok q)) :
    Nonempty (ParserTrace self byteOffset value offsetValues q) := by
  unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value at h
  rcases bind_ok_inv _ _ _ h with ⟨x0, hx0, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x1, hx1, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x2, hx2, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x3, hx3, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x4, hx4, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x5, hx5, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x6, hx6, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x7, hx7, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x8, hx8, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x9, hx9, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x10, hx10, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x11, hx11, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x12, hx12, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x13, hx13, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x14, hx14, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x15, hx15, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x16, hx16, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x17, hx17, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x18, hx18, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x19, hx19, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x20, hx20, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x21, hx21, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x22, hx22, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x23, hx23, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x24, hx24, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x25, hx25, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x26, hx26, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x27, hx27, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x28, hx28, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x29, hx29, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x30, hx30, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x31, hx31, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x32, hx32, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨x33, hx33, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨slice, hslice, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨parsed, hparsed, h⟩
  rcases bind_ok_inv _ _ _ h with ⟨offset, hoffset, h⟩
  cases ho : parsed with
  | none => simp [AspisR1DecodeKFullV10.core.option.Option.ok_or, ho] at h
  | some parsedValue =>
      simp only [AspisR1DecodeKFullV10.core.option.Option.ok_or, ho,
        Result.ok.injEq] at h
      cases h
      rw [ho] at hparsed
      exact ⟨{
        strideValue := x0, payloadStart := x1, finalOffset := offset, payloadData := x2, inputBytes := slice,
        p1 := x4, p2 := x6, p3 := x8, p4 := x10, p5 := x12,
        p6 := x14, p7 := x16, p8 := x18, p9 := x20, p10 := x22,
        p11 := x24, p12 := x26, p13 := x28, p14 := x30, p15 := x32,
        b0 := x3, b1 := x5, b2 := x7, b3 := x9, b4 := x11, b5 := x13,
        b6 := x15, b7 := x17, b8 := x19, b9 := x21, b10 := x23,
        b11 := x25, b12 := x27, b13 := x29, b14 := x31, b15 := x33,
        hoffsetMul := hx0, hstart := hx1, hpayload := hx2,
        hread0 := hx3, hp1 := hx4, hread1 := hx5, hp2 := hx6, hread2 := hx7,
        hp3 := hx8, hread3 := hx9, hp4 := hx10, hread4 := hx11,
        hp5 := hx12, hread5 := hx13, hp6 := hx14, hread6 := hx15,
        hp7 := hx16, hread7 := hx17, hp8 := hx18, hread8 := hx19,
        hp9 := hx20, hread9 := hx21, hp10 := hx22, hread10 := hx23,
        hp11 := hx24, hread11 := hx25, hp12 := hx26, hread12 := hx27,
        hp13 := hx28, hread13 := hx29, hp14 := hx30, hread14 := hx31,
        hp15 := hx32, hread15 := hx33, hinput := hslice, hparse := hparsed,
        hoffsetValues := hoffset
      }⟩

#print axioms decode_k_value_success_parser_trace
end AspisR1DecodeKFullValueTrace
