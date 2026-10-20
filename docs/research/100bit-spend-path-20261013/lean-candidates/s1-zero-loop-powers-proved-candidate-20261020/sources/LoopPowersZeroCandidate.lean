import LoopPowersCandidateTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1LoopPowers

@[global_simps, irreducible]
def field.WideExact.ZERO : field.WideExact :=
  { c0 := field.QM31.ZERO, c1 := field.QM31.ZERO }

def weights.powers_zero
  (N : Std.Usize) (x : field.WideExact) :
  Result (Array field.WideExact N)
  := do
  let out := Array.repeat N field.WideExact.ZERO
  weights.powers_loop x out field.WideExact.ONE 0#usize

theorem powers_zero_total_exact (N : Usize) (x : field.WideExact) (hx : Canonical x) :
    ∃ out, weights.powers_zero N x = .ok out ∧
      ∀ j : Fin N.val,
        Canonical (out.val[j.val]'(by rw [out.property]; exact j.isLt)) ∧
        decode (out.val[j.val]'(by rw [out.property]; exact j.isLt)) = decode x ^ j.val := by
  obtain ⟨out,hout,hpre⟩ := loop_total_exact x field.WideExact.ONE
    (Array.repeat N field.WideExact.ZERO) 0#usize hx (by scalar_tac) one_canonical
    (by simpa using one_decode) (by
      intro j hj
      change j.val < 0 at hj
      exact (Nat.not_lt_zero _ hj).elim)
  exact ⟨out,hout,fun j => hpre j j.isLt⟩

#print axioms powers_zero_total_exact
end AspisR1LoopPowers
