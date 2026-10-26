import RPz7_NP6_ClaimsModel
/-! Success inversion retains the same record and each actual decoder call.
No canonicality, chosen decoder output or independently accepted child is a
premise. This is an owned-reference law pending native P6. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsSuccess
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent NP6_StdModel

theorem decoded_rows (external : External) (vr : Record) (out : Claims)
    (accepted : decodeRows external vr = ok (.Ok out)) :
    ∃ row0 row1 row2,
      external.decode 29#usize vr 0#usize = ok (.Ok row0) ∧
      external.decode 29#usize vr 29#usize = ok (.Ok row1) ∧
      external.decode 29#usize vr 58#usize = ok (.Ok row2) ∧
      out.val = [row0,row1,row2] := by
  cases h0 : external.decode 29#usize vr 0#usize with
  | fail e => simp [decodeRows,h0] at accepted
  | div => simp [decodeRows,h0] at accepted
  | ok r0 =>
    cases r0 with
    | Err e => simp [decodeRows,h0] at accepted
    | Ok row0 =>
      cases h1 : external.decode 29#usize vr 29#usize with
      | fail e => simp [decodeRows,h0,h1] at accepted
      | div => simp [decodeRows,h0,h1] at accepted
      | ok r1 =>
        cases r1 with
        | Err e => simp [decodeRows,h0,h1] at accepted
        | Ok row1 =>
          cases h2 : external.decode 29#usize vr 58#usize with
          | fail e => simp [decodeRows,h0,h1,h2] at accepted
          | div => simp [decodeRows,h0,h1,h2] at accepted
          | ok r2 =>
            cases r2 with
            | Err e => simp [decodeRows,h0,h1,h2] at accepted
            | Ok row2 =>
              have contents : out.val = [row0,row1,row2] := by
                simp [decodeRows,h0,h1,h2] at accepted
                subst out
                rfl
              exact ⟨row0,row1,row2,rfl,rfl,rfl,contents⟩

theorem reference_success (reservation : Reservation) (pre : r1_wire.Prefix)
    (out : Claims)
    (accepted : claimsReference (ClaimsUnrolledFinish.external (calls reservation)) pre = ok (.Ok out)) :
    reservation = .Ok () ∧ ∃ vr row0 row1 row2,
      (ClaimsUnrolledFinish.external (calls reservation)).validated pre 25#u8 = ok (.Ok vr) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 0#usize = ok (.Ok row0) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 29#usize = ok (.Ok row1) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 58#usize = ok (.Ok row2) ∧
      out.val = [row0,row1,row2] := by
  rw [NP6_ClaimsModel.reference_normalized] at accepted
  cases hv : (ClaimsUnrolledFinish.external (calls reservation)).validated pre 25#u8 with
  | fail e => simp [NP6_ClaimsModel.normalized,hv] at accepted
  | div => simp [NP6_ClaimsModel.normalized,hv] at accepted
  | ok r =>
    cases r with
    | Err e => simp [NP6_ClaimsModel.normalized,hv] at accepted
    | Ok vr =>
      cases reservation with
      | Err e => simp [NP6_ClaimsModel.normalized,hv] at accepted
      | Ok u =>
        cases u
        have hd : decodeRows (ClaimsUnrolledFinish.external (calls (.Ok ()))) vr = ok (.Ok out) := by
          simpa [NP6_ClaimsModel.normalized,hv] using accepted
        obtain ⟨row0,row1,row2,h0,h1,h2,contents⟩ := decoded_rows _ vr out hd
        exact ⟨rfl,vr,row0,row1,row2,rfl,h0,h1,h2,contents⟩

#print axioms decoded_rows
#print axioms reference_success
end AspisR1.NP6_ClaimsSuccess
end
