import R1Z.ProverRw19ByteLength
import R1Z.ProverRw19AuditValue
set_option autoImplicit false
namespace R1Z.ProverRw19BodyLengthValue
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw19AuditValue (Status)

def HasLength {S : Type} (n : Nat) : Result (Status × S) → Prop
  | .ok (.Ok (bytes,_), _) => bytes.val.length = n
  | .ok (.Err _, _) | .fail _ | .div => True

theorem bind_good {A S : Type} (n : Nat) (r : Result A) (f : A → Result (Status × S))
    (good : ∀ value, HasLength n (f value)) : HasLength n (r >>= f) := by
  cases r with
  | ok value => exact good value
  | fail e => trivial
  | div => trivial

def finish {S : Type} (r : Result ProverRw19ByteLength.ByteStatus)
    (audit : prover.MaskedFixtureAudit) (after : S) : Result (Status × S) := do
  let status ← r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch status
  match cf with
  | .Continue bytes => ok (.Ok (bytes,audit),after)
  | .Break residual =>
    let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) residual
    ok (status,after)

theorem finish_good {S : Type} (n : Nat) (r : Result ProverRw19ByteLength.ByteStatus)
    (audit : prover.MaskedFixtureAudit) (after : S)
    (good : ProverRw19ByteLength.HasLength n r) : HasLength n (finish r audit after) := by
  cases r with
  | fail e => trivial
  | div => trivial
  | ok status => cases status <;> exact good

theorem rejected {S : Type} (n : Nat) (error : verifier.Error) (after : S) :
    HasLength n (ok (.Err error,after)) := trivial

theorem residual {S : Type} (n : Nat)
    (r : core.result.Result core.convert.Infallible verifier.Error) (after : S) :
    HasLength n (do
      let status ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) r
      ok (status,after)) := by
  cases r with
  | Ok impossible => cases impossible
  | Err e => trivial

#print axioms bind_good
#print axioms finish_good
#print axioms rejected
#print axioms residual
end R1Z.ProverRw19BodyLengthValue
