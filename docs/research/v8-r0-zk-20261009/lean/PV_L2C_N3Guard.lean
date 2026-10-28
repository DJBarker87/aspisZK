import PV_L2C_BaseGuard
import PV_L2C_SecureGuard
set_option autoImplicit false
namespace PV_L2C_N3Guard
open Aeneas Aeneas.Std Result
inductive Failure where
  | publicError

def baseAll (base : Fin 26 → List U32) : List (Fin 26) → Except Failure Unit
  | [] => .ok ()
  | c::cs => match PV_L2C_BaseGuard.check (base c) with
    | .error _ => .error .publicError
    | .ok () => baseAll base cs

def secure (column : Nat → PV_L2C_NativeQ.Q) : Result (Except Failure Unit) := do
  let r ← PV_L2C_SecureGuard.loop 1024 0 column
  match r with
  | .error _ => ok (.error .publicError)
  | .ok () => ok (.ok ())

/-- The exact three-call guard cut: base columns, then d, then g. All error
arms are retained. Header, material and observation associations are separate. -/
def run (base : Fin 26 → List U32) (d g : Nat → PV_L2C_NativeQ.Q) :
    Result (Except Failure Unit) :=
  match baseAll base (List.finRange 26) with
  | .error e => ok (.error e)
  | .ok () => do
    let dr ← secure d
    match dr with
    | .error e => ok (.error e)
    | .ok () => secure g

theorem base_expected (base : Fin 26 → List U32)
    (h : ∀ c, PV_L2C_BaseGuard.check (base c) = .ok ()) (cs : List (Fin 26)) :
    baseAll base cs = .ok () := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [baseAll,h c];exact ih
#print axioms base_expected

theorem expected (base : Fin 26 → List U32) (d g : Nat → PV_L2C_NativeQ.Q)
    (hb : ∀ c, PV_L2C_BaseGuard.check (base c) = .ok ())
    (hd : PV_L2C_SecureGuard.loop 1024 0 d = ok (.ok ()))
    (hg : PV_L2C_SecureGuard.loop 1024 0 g = ok (.ok ())) : run base d g = ok (.ok ()) := by
  rw [run,base_expected base hb]
  simp only [secure,hd,hg,bind_tc_ok]
#print axioms expected
end PV_L2C_N3Guard
