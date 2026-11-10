-- PCVS_ item (3): op17 with the three aspis-core callees taken from the frozen 4bb3b3f emission (PCVS_E001) instead of bound to the gate constants.
-- powersF is the PRVEq_Op17_p2 loop text with WideExact.mul/ZERO/ONE replaced by the fresh frozen callees behind the nominal port toF/fromF.
import Aeneas
import PRVEq_WideBind_s2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVS_Op17
open AspisR1LoopPowers PCVS_Eq
abbrev W := AspisR1LoopPowers.field.WideExact

def mulF (x y : W) : Result W := do
  let z ← PCVS_Fresh.field.wide_exact.WideExact.mul (toF x) (toF y)
  ok (fromF z)
def zeroF : W := fromF PCVS_Fresh.field.wide_exact.WideExact.ZERO
def oneF : W := fromF PCVS_Fresh.field.wide_exact.WideExact.ONE

def powersF_loop.body {N : Std.Usize} (x : W) (out : Array W N) (p : W) (i : Std.Usize) :
  Result (ControlFlow ((Array W N) × W × Std.Usize) ((Array W N) × (Option (Array W N)))) := do
  if i < N
  then
    let (_, index_mut_back) ← Array.index_mut_usize out i
    let i1 ← i + 1#usize
    if i1 = N
    then let out1 := index_mut_back p
         ok (done (out1, some out1))
    else
      let p1 ← mulF p x
      let out1 := index_mut_back p
      ok (cont (out1, p1, i1))
  else ok (done (out, none))

def powersF_loop {N : Std.Usize} (x : W) (out : Array W N) (p : W) (i : Std.Usize) :
  Result ((Array W N) × (Option (Array W N))) := do
  loop (fun (out1, p1, i1) => powersF_loop.body x out1 p1 i1) (out, p, i)

def powersF (N : Std.Usize) (x : W) : Result (Array W N) := do
  let we ← ok zeroF
  let out := Array.repeat N we
  let p ← ok oneF
  let (out1, pending_return) ← powersF_loop x out p 0#usize
  match pending_return with
  | none => ok out1
  | some out2 => ok out2

theorem mulF_eq : mulF = AspisR1LoopPowers.field.WideExact.mul := by
  funext x y; exact bind_mul x y
theorem zeroF_eq : zeroF = AspisR1LoopPowers.field.WideExact.ZERO := bind_zero
theorem oneF_eq : oneF = AspisR1LoopPowers.field.WideExact.ONE := bind_one

theorem powersF_eq (N : Std.Usize) (x : W) : powersF N x = AspisR1LoopPowers.PCVN_FreshPowers.powers N x := by
  unfold powersF AspisR1LoopPowers.PCVN_FreshPowers.powers powersF_loop AspisR1LoopPowers.PCVN_FreshPowers.powers_loop
    powersF_loop.body AspisR1LoopPowers.PCVN_FreshPowers.powers_loop.body
  rw [mulF_eq, zeroF_eq, oneF_eq]

/-- op17 with the frozen callees: the Tx2N_Powers slot equals the frozen weights::powers text over the frozen WideExact mul/ZERO/ONE. -/
theorem op17_frozen_bound (N : Std.Usize) (x : AspisR1.Tx2N_Powers.E) :
    AspisR1.Tx2N_Powers.powers N x = (do
      let out ← powersF N (AspisR1.Tx2N_Powers.toPowers x)
      ok (AspisR1.Tx2N_Powers.mapArray out)) := by
  rw [powersF_eq]
  exact AspisR1LoopPowers.PCVN_Op17.op17_frozen N x

#print axioms op17_frozen_bound
end PCVS_Op17
