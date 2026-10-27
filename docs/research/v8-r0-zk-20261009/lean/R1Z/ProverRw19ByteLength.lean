import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.ProverRw19ByteLength
open Aeneas Aeneas.Std Result ProverRwFull
abbrev ByteStatus := core.result.Result (alloc.vec.Vec U8) verifier.Error

def HasLength (n : Nat) : Result ByteStatus → Prop
  | .ok (.Ok bytes) => bytes.val.length = n
  | .ok (.Err _) | .fail _ | .div => True

theorem bind_good {A : Type} (n : Nat) (r : Result A) (f : A → Result ByteStatus)
    (good : ∀ value, HasLength n (f value)) : HasLength n (r >>= f) := by
  cases r with
  | ok value => exact good value
  | fail e => trivial
  | div => trivial

theorem guarded (n : Nat) (condition : Prop) [Decidable condition]
    (tail : Result ByteStatus) (good : condition → HasLength n tail) :
    HasLength n (do massert condition; tail) := by
  unfold massert
  split
  · simpa only [bind_tc_ok] using good ‹condition›
  · trivial

theorem successful (bytes : alloc.vec.Vec U8) (size : Usize)
    (length : alloc.vec.Vec.len bytes = size) :
    HasLength size.val (.ok (.Ok bytes)) := by
  change bytes.val.length = size.val
  exact congrArg UScalar.val length

theorem residual (n : Nat) (r : core.result.Result core.convert.Infallible verifier.Error) :
    HasLength n
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) r) := by
  cases r with
  | Ok impossible => cases impossible
  | Err e => trivial

#print axioms bind_good
#print axioms guarded
#print axioms successful
#print axioms residual
end R1Z.ProverRw19ByteLength
