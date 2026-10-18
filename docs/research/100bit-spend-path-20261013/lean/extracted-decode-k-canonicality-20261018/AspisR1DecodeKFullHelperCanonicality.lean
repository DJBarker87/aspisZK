import AspisR1DecodeKFullV10.Funs
import AspisR1DecodeKFullParserCanonicalityCMQ

set_option autoImplicit false

namespace AspisR1DecodeKFullHelperCanonicality

open Aeneas Aeneas.Std Result

private theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = Result.ok y) :
    ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem decode_k_value_success_canonical
    (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byte_offset value offset_values : Usize) (q : AspisR1DecodeKFullV10.aspis_core.field.QM31)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
      self byte_offset value offset_values =
      Result.ok (core.result.Result.Ok q)) :
    q.c0.a.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
    q.c0.b.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
    q.c1.a.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
    q.c1.b.val < AspisR1DecodeKFullV10.aspis_core.field.P.val := by
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
  | some value =>
      simp only [AspisR1DecodeKFullV10.core.option.Option.ok_or, ho,
        Result.ok.injEq] at h
      cases h
      rw [ho] at hparsed
      exact AspisR1DecodeKFullParserCanonicality.qm31_from_le_bytes_success_canonical _ _ hparsed

#print axioms decode_k_value_success_canonical

end AspisR1DecodeKFullHelperCanonicality
