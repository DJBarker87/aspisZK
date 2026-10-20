import CurrentWidePolynomialHornerListV10
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

private theorem callback_bind_ok_inv {α β : Type}
    {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Typed current-Wide adapter for the exact extracted polynomial callback
    order: multiply the accumulator by the captured challenge, perform the
    coefficient lookup, then add that coefficient. -/
def current_polynomial_call_mut
    (lookup : Slice Std.U8 → Std.Usize → Result field.wide_exact.WideExact)
    (state : field.wide_exact.WideExact × Slice Std.U8)
    (args : field.wide_exact.WideExact × Std.Usize) :
    Result (field.wide_exact.WideExact ×
      (field.wide_exact.WideExact × Slice Std.U8)) := do
  let product ← field.wide_exact.WideExact.mul args.1 state.1
  let coefficient ← lookup state.2 args.2
  let next ← field.wide_exact.WideExact.add product coefficient
  ok (next, state)

theorem current_polynomial_call_mut_success
    (lookup : Slice Std.U8 → Std.Usize → Result field.wide_exact.WideExact)
    (state : field.wide_exact.WideExact × Slice Std.U8)
    (args : field.wide_exact.WideExact × Std.Usize)
    (out : field.wide_exact.WideExact)
    (hmultiplier : CanonicalWide state.1)
    (hacc : CanonicalWide args.1)
    (hlookup : ∀ bytes i c, lookup bytes i = .ok c → CanonicalWide c)
    (hcall : current_polynomial_call_mut lookup state args = .ok (out, state)) :
    ∃ coefficient, lookup state.2 args.2 = .ok coefficient ∧
      CanonicalWide coefficient ∧ CanonicalWide out ∧
      decodeWide out = decodeWide args.1 * decodeWide state.1 +
        decodeWide coefficient := by
  rcases callback_bind_ok_inv hcall with ⟨product, hp, hrest⟩
  rcases callback_bind_ok_inv hrest with ⟨coefficient, hc, hrest⟩
  rcases callback_bind_ok_inv hrest with ⟨next, ha, hout⟩
  have hnext : next = out := by
    have he := Result.ok.inj hout
    exact congrArg Prod.fst he
  subst out
  have hstep := current_horner_step_success args.1 state.1 coefficient next
    hacc hmultiplier (hlookup state.2 args.2 coefficient hc) (by
      change Bind.bind (field.wide_exact.WideExact.mul args.1 state.1)
        (fun product => field.wide_exact.WideExact.add product coefficient) = .ok next
      rw [hp]
      exact ha)
  exact ⟨coefficient, hc, hlookup state.2 args.2 coefficient hc,
    hstep.1, hstep.2⟩

#print axioms current_polynomial_call_mut_success

end AspisR1CurrentWide.Proof
