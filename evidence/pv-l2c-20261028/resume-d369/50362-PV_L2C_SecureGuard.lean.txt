import PV_L2C_QParser
import PV_L2C_NativeQ
set_option autoImplicit false
namespace PV_L2C_SecureGuard
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71 PV_L2C_NativeQ
inductive Failure where
  | publicError

def word (q : Q) (j : Fin 4) : U32 := ⟨q j⟩
def bytes (q : Q) := PV_L2C_ParserHalves8.pair
  (PV_L2C_QParser.complexBytes (word q 0) (word q 1))
  (PV_L2C_QParser.complexBytes (word q 2) (word q 3))

def one (q : Q) : Result (Except Failure Unit) := do
  let parsed ← aspis_core.field.QM31.from_le_bytes (bytes q)
  match parsed with
  | none => ok (.error .publicError)
  | some _ => ok (.ok ())

theorem roundtrip (q : Q) (hq : Canonical q) :
    aspis_core.field.QM31.from_le_bytes (bytes q) =
      ok (some ⟨⟨word q 0,word q 1⟩,⟨word q 2,word q 3⟩⟩) :=
  PV_L2C_QParser.parse _ _ _ _ (hq 0) (hq 1) (hq 2) (hq 3)
#print axioms roundtrip

theorem expected (q : Q) (hq : Canonical q) : one q = ok (.ok ()) := by
  rw [one,roundtrip q hq]
  rfl
#print axioms expected

def loop : Nat → Nat → (Nat → Q) → Result (Except Failure Unit)
  | 0,_,_ => ok (.ok ())
  | n+1,start,column => do
    let result ← one (column start)
    match result with
    | .error e => ok (.error e)
    | .ok () => loop n (start+1) column

theorem column (n start : Nat) (table : Nat → Q)
    (hc : ∀ j, start ≤ j → j < start+n → Canonical (table j)) :
    loop n start table = ok (.ok ()) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [loop,expected _ (hc start (by omega) (by omega))]
    simp only [bind_tc_ok]
    exact ih (start+1) (by intro j hj hj';exact hc j (by omega) (by omega))
#print axioms column
end PV_L2C_SecureGuard
