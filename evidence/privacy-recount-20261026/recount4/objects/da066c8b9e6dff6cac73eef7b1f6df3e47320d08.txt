import R1Z.ProverRwBodyStoreSource
set_option autoImplicit false
namespace R1Z.ProverRw19AuditValue
open Aeneas Aeneas.Std Result ProverRwFull

-- The mathematical audit of an admitted successful proof. This definition
-- neither calls the prover nor obtains a field from an actual source result.
def canonical : prover.MaskedFixtureAudit :=
  ⟨16#usize, 10#usize, true, true, true, true⟩

theorem guarded (audit : prover.MaskedFixtureAudit)
    (c1 : audit.c1_columns_inactive_balanced = 16#usize)
    (mask : audit.mask_only_columns_inactive_balanced = 10#usize)
    (d : audit.d_inactive_balanced = true)
    (g : audit.g_inactive_balanced = true)
    (padding : audit.h1_padding_inactive_balanced = true) :
    {audit with h1_total_balanced := true} = canonical := by
  cases audit
  cases c1
  cases mask
  cases d
  cases g
  cases padding
  rfl

abbrev Status := core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error

-- This only constrains successful audit values. Error, failure and divergence
-- correspondence remains part of the complete two-observation criterion.
def Good {S : Type} : Result (Status × S) → Prop
  | .ok (.Ok (_, audit), _) => audit = canonical
  | .ok (.Err _, _) | .fail _ | .div => True

theorem bind_good {A S : Type} (r : Result A) (f : A → Result (Status × S))
    (hf : ∀ a, Good (f a)) : Good (r >>= f) := by
  cases r with
  | ok a => exact hf a
  | fail e => trivial
  | div => trivial

theorem rejected {S : Type} (error : verifier.Error) (after : S) :
    Good (ok (.Err error, after)) := trivial

theorem successful {S : Type} (bytes : alloc.vec.Vec U8)
    (audit : prover.MaskedFixtureAudit) (after : S)
    (c1 : audit.c1_columns_inactive_balanced = 16#usize)
    (mask : audit.mask_only_columns_inactive_balanced = 10#usize)
    (d : audit.d_inactive_balanced = true)
    (g : audit.g_inactive_balanced = true)
    (padding : audit.h1_padding_inactive_balanced = true) :
    Good (ok (.Ok (bytes, {audit with h1_total_balanced := true}), after)) :=
  guarded audit c1 mask d g padding

theorem residual {S : Type} (r : core.result.Result core.convert.Infallible verifier.Error)
    (after : S) :
    Good (do
      let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) r
      ok (status, after)) := by
  cases r with
  | Ok impossible => cases impossible
  | Err error => trivial

#print axioms guarded
#print axioms bind_good
#print axioms rejected
#print axioms successful
#print axioms residual
end R1Z.ProverRw19AuditValue
