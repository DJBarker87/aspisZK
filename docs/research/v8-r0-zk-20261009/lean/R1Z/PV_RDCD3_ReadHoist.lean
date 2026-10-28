import R1Z.PV_RDCD3_RangeFold

namespace R1Z.PV_RDCD3_ReadHoist
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDCD3_RangeFold

/-- Repeated reads of one immutable array location in each iteration. -/
def repeated {T S : Type} (read : Result T) (f : T → S → Nat → Result S)
    (n start : Nat) (acc : S) : Result S :=
  ordered (fun a i => do let x ← read; f x a i) n start acc

def hoisted {T S : Type} (read : Result T) (f : T → S → Nat → Result S)
    (n start : Nat) (acc : S) : Result S := do
  let x ← read
  ordered (f x) n start acc

/-- Nonemptiness is essential: an invalid dimension read must fail in the first
source iteration. This proves the complete carrier law even when read fails or
when it diverges. It does not hoist an effectful world operation. -/
theorem nonempty {T S : Type} (read : Result T) (f : T → S → Nat → Result S)
    (n start : Nat) (acc : S) (positive : 0 < n) :
    repeated read f n start acc = hoisted read f n start acc := by
  cases read with
  | ok x => rfl
  | fail e =>
    cases n with
    | zero => omega
    | succ n => simp [repeated,hoisted,ordered]
  | div =>
    cases n with
    | zero => omega
    | succ n => simp [repeated,hoisted,ordered]

/-- The empty-loop behavior is retained, explaining why the proof must use the
actual five/ten iteration source bounds instead of an arbitrary-length claim. -/
theorem empty {T S : Type} (read : Result T) (f : T → S → Nat → Result S)
    (start : Nat) (acc : S) : repeated read f 0 start acc = ok acc := rfl

#print axioms nonempty
#print axioms empty
end R1Z.PV_RDCD3_ReadHoist
