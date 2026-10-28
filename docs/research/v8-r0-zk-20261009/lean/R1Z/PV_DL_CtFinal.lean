import R1Z.PV_DL_Forwarding
import R1Z.PV_DL_ArrayShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_CtFinal
set_option autoImplicit false
abbrev Side := ProverRwFull.digest.core_api.TruncSide

/-- Initialize the temporary full output, preserve both mutable returns, read
TRUNC_SIDE after the variable finalizer, then copy exactly the selected span. -/
def reference {S B : Type} (initial : Result (List U8))
    (finish : S → B → List U8 → Result (S × B × List U8))
    (side : Result Side) (n : Nat) (state : S) (buffer : B) : Result (S × B × List U8) := do
  let full ← initial
  let (state,buffer,full) ← finish state buffer full
  let side ← side
  if n≤full.length then ok (state,buffer,PV_DL_Truncation.value side n full)
  else fail .panic

def value {S B : Type} (initial : Result (List U8))
    (finish : S → B → List U8 → Result (S × B × List U8))
    (side : Result Side) (n : Nat) (state : S) (buffer : B) : Result (S × B × List U8) :=
  match initial with
  | .fail e => fail e
  | .div => div
  | .ok full =>
    match finish state buffer full with
    | .fail e => fail e
    | .div => div
    | .ok (changed,restored,full) =>
      match side with
      | .fail e => fail e
      | .div => div
      | .ok side => if n≤full.length then ok (changed,restored,PV_DL_Truncation.value side n full)
        else fail .panic

theorem complete {S B : Type} (initial : Result (List U8))
    (finish : S → B → List U8 → Result (S × B × List U8))
    (side : Result Side) (n : Nat) (state : S) (buffer : B) :
    reference initial finish side n state buffer=value initial finish side n state buffer := by
  cases hi : initial with
  | fail e => simp only [reference,value,hi,bind_tc_fail]
  | div => simp only [reference,value,hi,bind_tc_div]
  | ok full =>
    simp only [reference,value,hi,bind_tc_ok]
    cases hf : finish state buffer full with
    | fail e => simp only [hf,bind_tc_fail]
    | div => simp only [hf,bind_tc_div]
    | ok result => rcases result with ⟨changed,restored,bytes⟩;cases side <;> rfl

theorem restoration {S B : Type} (initial : Result (List U8))
    (finish : S → B → List U8 → Result (S × B × List U8))
    (side : Result Side) (n : Nat) (state changed : S) (buffer restored : B)
    (seed full : List U8) (direction : Side)
    (hi : initial=ok seed) (hf : finish state buffer seed=ok (changed,restored,full))
    (hs : side=ok direction) (hn : n≤full.length) :
    reference initial finish side n state buffer=
      ok (changed,restored,PV_DL_Truncation.value direction n full) := by
  simp only [reference,hi,hf,hs,bind_tc_ok,Aeneas.Std.uncurry,if_pos hn]

theorem output_shape (s : PV_DL_ArrayShape.Shape) (side : Side) (full : List U8)
    (h : PV_DL_ArrayShape.size s≤full.length) :
    PV_DL_ArrayShape.flatten s
      (PV_DL_ArrayShape.build s (fun i => (PV_DL_Truncation.value side (PV_DL_ArrayShape.size s) full)[i]!))=
      PV_DL_Truncation.value side (PV_DL_ArrayShape.size s) full :=
  PV_DL_ArrayShape.reconstruct s _ (PV_DL_Truncation.length side _ full h)

#print axioms reference
#print axioms value
#print axioms complete
#print axioms restoration
#print axioms output_shape
end R1Z.PV_DL_CtFinal
