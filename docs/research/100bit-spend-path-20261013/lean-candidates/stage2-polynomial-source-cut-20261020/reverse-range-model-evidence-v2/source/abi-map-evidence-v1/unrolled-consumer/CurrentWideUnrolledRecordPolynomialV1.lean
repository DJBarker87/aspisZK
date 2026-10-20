import CurrentWideActualRecordFieldCallbackV1
import CurrentWidePolynomialHornerListV10
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

/-- Verbatim ordered current-Wide port of the frozen generated seven-bind
    polynomial body. Generated nominal types are mapped through the pinned ABI
    adapter; generated fail stubs/external templates are not imported. -/
def current_unrolled_record_polynomial (bytes : Slice U8) (x : E) : Result E := do
  let we ← field.wide_exact.WideExact.mul currentWideZero x
  let we1 ← currentRecordFieldLookupNat bytes 6
  let a ← field.wide_exact.WideExact.add we we1
  let we2 ← field.wide_exact.WideExact.mul a x
  let we3 ← currentRecordFieldLookupNat bytes 5
  let a1 ← field.wide_exact.WideExact.add we2 we3
  let we4 ← field.wide_exact.WideExact.mul a1 x
  let we5 ← currentRecordFieldLookupNat bytes 4
  let a2 ← field.wide_exact.WideExact.add we4 we5
  let we6 ← field.wide_exact.WideExact.mul a2 x
  let we7 ← currentRecordFieldLookupNat bytes 3
  let a3 ← field.wide_exact.WideExact.add we6 we7
  let we8 ← field.wide_exact.WideExact.mul a3 x
  let we9 ← currentRecordFieldLookupNat bytes 2
  let a4 ← field.wide_exact.WideExact.add we8 we9
  let we10 ← field.wide_exact.WideExact.mul a4 x
  let we11 ← currentRecordFieldLookupNat bytes 1
  let a5 ← field.wide_exact.WideExact.add we10 we11
  let we12 ← field.wide_exact.WideExact.mul a5 x
  let we13 ← currentRecordFieldLookupNat bytes 0
  field.wide_exact.WideExact.add we12 we13

private theorem bind_ok_inv {α β : Type} {r : Result α}
    {f : α → Result β} {out : β}
    (h : Bind.bind r f = .ok out) : ∃ a, r = .ok a ∧ f a = .ok out := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem current_unrolled_record_polynomial_success
    (bytes : Slice U8) (x out : E)
    (hx : CanonicalWide x)
    (hpoly : current_unrolled_record_polynomial bytes x = .ok out) :
    CanonicalWide out ∧ ∃ coefficients,
      (∀ c ∈ coefficients, CanonicalWide c) ∧
      List.Forall₂ (fun i c => currentRecordFieldLookupNat bytes i = .ok c)
        [6,5,4,3,2,1,0] coefficients ∧
      decodeWide out = horner_value 0 (decodeWide x) (coefficients.map decodeWide) := by
  change (do
    let we ← field.wide_exact.WideExact.mul currentWideZero x
    let we1 ← currentRecordFieldLookupNat bytes 6
    let a ← field.wide_exact.WideExact.add we we1
    let we2 ← field.wide_exact.WideExact.mul a x
    let we3 ← currentRecordFieldLookupNat bytes 5
    let a1 ← field.wide_exact.WideExact.add we2 we3
    let we4 ← field.wide_exact.WideExact.mul a1 x
    let we5 ← currentRecordFieldLookupNat bytes 4
    let a2 ← field.wide_exact.WideExact.add we4 we5
    let we6 ← field.wide_exact.WideExact.mul a2 x
    let we7 ← currentRecordFieldLookupNat bytes 3
    let a3 ← field.wide_exact.WideExact.add we6 we7
    let we8 ← field.wide_exact.WideExact.mul a3 x
    let we9 ← currentRecordFieldLookupNat bytes 2
    let a4 ← field.wide_exact.WideExact.add we8 we9
    let we10 ← field.wide_exact.WideExact.mul a4 x
    let we11 ← currentRecordFieldLookupNat bytes 1
    let a5 ← field.wide_exact.WideExact.add we10 we11
    let we12 ← field.wide_exact.WideExact.mul a5 x
    let we13 ← currentRecordFieldLookupNat bytes 0
    field.wide_exact.WideExact.add we12 we13) = .ok out at hpoly
  rcases bind_ok_inv hpoly with ⟨p6, hm6, h⟩
  rcases bind_ok_inv h with ⟨c6, hc6run, h⟩
  rcases bind_ok_inv h with ⟨a6, ha6run, h⟩
  rcases bind_ok_inv h with ⟨p5, hm5, h⟩
  rcases bind_ok_inv h with ⟨c5, hc5run, h⟩
  rcases bind_ok_inv h with ⟨a5, ha5run, h⟩
  rcases bind_ok_inv h with ⟨p4, hm4, h⟩
  rcases bind_ok_inv h with ⟨c4, hc4run, h⟩
  rcases bind_ok_inv h with ⟨a4, ha4run, h⟩
  rcases bind_ok_inv h with ⟨p3, hm3, h⟩
  rcases bind_ok_inv h with ⟨c3, hc3run, h⟩
  rcases bind_ok_inv h with ⟨a3, ha3run, h⟩
  rcases bind_ok_inv h with ⟨p2, hm2, h⟩
  rcases bind_ok_inv h with ⟨c2, hc2run, h⟩
  rcases bind_ok_inv h with ⟨a2, ha2run, h⟩
  rcases bind_ok_inv h with ⟨p1, hm1, h⟩
  rcases bind_ok_inv h with ⟨c1, hc1run, h⟩
  rcases bind_ok_inv h with ⟨a1, ha1run, h⟩
  rcases bind_ok_inv h with ⟨p0, hm0, h⟩
  rcases bind_ok_inv h with ⟨c0, hc0run, houtRun⟩
  have hcoef6 := currentRecordFieldLookupNat_success_canonical bytes 6 c6 hc6run
  have hcoef5 := currentRecordFieldLookupNat_success_canonical bytes 5 c5 hc5run
  have hcoef4 := currentRecordFieldLookupNat_success_canonical bytes 4 c4 hc4run
  have hcoef3 := currentRecordFieldLookupNat_success_canonical bytes 3 c3 hc3run
  have hcoef2 := currentRecordFieldLookupNat_success_canonical bytes 2 c2 hc2run
  have hcoef1 := currentRecordFieldLookupNat_success_canonical bytes 1 c1 hc1run
  have hcoef0 := currentRecordFieldLookupNat_success_canonical bytes 0 c0 hc0run
  have hs6 : (do
      let p ← field.wide_exact.WideExact.mul currentWideZero x
      field.wide_exact.WideExact.add p c6) = .ok a6 := by
    change Bind.bind (field.wide_exact.WideExact.mul currentWideZero x)
      (fun p => field.wide_exact.WideExact.add p c6) = .ok a6
    rw [hm6]; exact ha6run
  have hs5 : (do
      let p ← field.wide_exact.WideExact.mul a6 x
      field.wide_exact.WideExact.add p c5) = .ok a5 := by
    change Bind.bind (field.wide_exact.WideExact.mul a6 x)
      (fun p => field.wide_exact.WideExact.add p c5) = .ok a5
    rw [hm5]; exact ha5run
  have hs4 : (do
      let p ← field.wide_exact.WideExact.mul a5 x
      field.wide_exact.WideExact.add p c4) = .ok a4 := by
    change Bind.bind (field.wide_exact.WideExact.mul a5 x)
      (fun p => field.wide_exact.WideExact.add p c4) = .ok a4
    rw [hm4]; exact ha4run
  have hs3 : (do
      let p ← field.wide_exact.WideExact.mul a4 x
      field.wide_exact.WideExact.add p c3) = .ok a3 := by
    change Bind.bind (field.wide_exact.WideExact.mul a4 x)
      (fun p => field.wide_exact.WideExact.add p c3) = .ok a3
    rw [hm3]; exact ha3run
  have hs2 : (do
      let p ← field.wide_exact.WideExact.mul a3 x
      field.wide_exact.WideExact.add p c2) = .ok a2 := by
    change Bind.bind (field.wide_exact.WideExact.mul a3 x)
      (fun p => field.wide_exact.WideExact.add p c2) = .ok a2
    rw [hm2]; exact ha2run
  have hs1 : (do
      let p ← field.wide_exact.WideExact.mul a2 x
      field.wide_exact.WideExact.add p c1) = .ok a1 := by
    change Bind.bind (field.wide_exact.WideExact.mul a2 x)
      (fun p => field.wide_exact.WideExact.add p c1) = .ok a1
    rw [hm1]; exact ha1run
  have hs0 : (do
      let p ← field.wide_exact.WideExact.mul a1 x
      field.wide_exact.WideExact.add p c0) = .ok out := by
    change Bind.bind (field.wide_exact.WideExact.mul a1 x)
      (fun p => field.wide_exact.WideExact.add p c0) = .ok out
    rw [hm0]; exact houtRun
  have hzero := currentWideZero_canonical
  have hstep6 := current_horner_step_success currentWideZero x c6 a6
    hzero hx hcoef6 hs6
  have hstep5 := current_horner_step_success a6 x c5 a5
    hstep6.1 hx hcoef5 hs5
  have hstep4 := current_horner_step_success a5 x c4 a4
    hstep5.1 hx hcoef4 hs4
  have hstep3 := current_horner_step_success a4 x c3 a3
    hstep4.1 hx hcoef3 hs3
  have hstep2 := current_horner_step_success a3 x c2 a2
    hstep3.1 hx hcoef2 hs2
  have hstep1 := current_horner_step_success a2 x c1 a1
    hstep2.1 hx hcoef1 hs1
  have hstep0 := current_horner_step_success a1 x c0 out
    hstep1.1 hx hcoef0 hs0
  have hcoeff : ∀ c ∈ [c6,c5,c4,c3,c2,c1,c0], CanonicalWide c := by
    intro c hc
    simp at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcoef6
    · exact hcoef5
    · exact hcoef4
    · exact hcoef3
    · exact hcoef2
    · exact hcoef1
    · exact hcoef0
  have htrace : List.Forall₂
      (fun i c => currentRecordFieldLookupNat bytes i = .ok c)
      [6,5,4,3,2,1,0] [c6,c5,c4,c3,c2,c1,c0] := by
    exact List.Forall₂.cons hc6run <| List.Forall₂.cons hc5run <|
      List.Forall₂.cons hc4run <| List.Forall₂.cons hc3run <|
      List.Forall₂.cons hc2run <| List.Forall₂.cons hc1run <|
      List.Forall₂.cons hc0run List.Forall₂.nil
  refine ⟨hstep0.1, [c6,c5,c4,c3,c2,c1,c0], hcoeff, htrace, ?_⟩
  rw [hstep0.2, hstep1.2, hstep2.2, hstep3.2, hstep4.2, hstep5.2, hstep6.2]
  simp [horner_value, currentWideZero_decodes_zero]

#print axioms current_unrolled_record_polynomial_success
end AspisR1CurrentWide.Proof
