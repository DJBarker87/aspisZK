import EbyKPushExplicitTypesV1
import AspisR1EbyKPushExplicitOpsV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1EbyKCheckedQAllParamV1

abbrev Q := AspisR1EbyKPushCutV3.fast_pairing.canonical.Q
abbrev Qm := AspisR1EbyKPushCutV3.field.QM31
abbrev Closure := AspisR1EbyKPushCutV3.fast_pairing.canonical.Q.from_limbs.closure
abbrev IterU32 := core.slice.iter.Iter Std.U32
abbrev FnMutU32 := core.ops.function.FnMut Closure Std.U32 Bool
abbrev IterAll := FnMutU32 → IterU32 → Closure → Result (Bool × IterU32)

@[global_simps, irreducible]
def P : Std.U32 := 2147483647#u32

def fromLimbsClosureCallMut (c : Closure) (tupled_args : Std.U32) :
    Result (Bool × Closure) := do
  ok (tupled_args < P, c)

def fromLimbsClosureCallOnce (c : Closure) (i : Std.U32) : Result Bool := do
  let (b, _) ← fromLimbsClosureCallMut c i
  ok b

@[reducible]
def fromLimbsClosureFnOnce : core.ops.function.FnOnce Closure Std.U32 Bool :=
  { call_once := fromLimbsClosureCallOnce }

@[reducible]
def fromLimbsClosureFnMut : FnMutU32 :=
  { FnOnceInst := fromLimbsClosureFnOnce,
    call_mut := fromLimbsClosureCallMut }

def limbsOf (k : Qm) : Result (Array Std.U32 4#usize) := do
  let i := k.c0.a
  let i1 := k.c0.b
  let i2 := k.c1.a
  let i3 := k.c1.b
  ok (Array.make 4#usize [i, i1, i2, i3])

def fromLimbsWithAll (all : IterAll) (x : Array Std.U32 4#usize) :
    Result (Option Q) := do
  let s ← lift (Array.to_slice x)
  let i ← core.slice.Slice.iter s
  let (b, _) ← all fromLimbsClosureFnMut i ()
  if b then ok (some x) else ok none

def optionOkOr {T E : Type} (self : Option T) (err : E) :
    Result (core.result.Result T E) := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

def checkedQWithAll (all : IterAll) (k : Qm) :
    Result (core.result.Result Q Unit) := do
  let a ← limbsOf k
  let o ← fromLimbsWithAll all a
  optionOkOr o ()

private theorem result_bind_ok_inv {α β : Type} (r : Result α)
    (f : α → Result β) (y : β) (h : Bind.bind r f = Result.ok y) :
    ∃ x, r = Result.ok x ∧ f x = Result.ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind, Aeneas.Std.bind] at h
  | div => simp [Bind.bind, Aeneas.Std.bind] at h

theorem fromLimbsWithAll_success_identity (all : IterAll)
    (x q : Q) (h : fromLimbsWithAll all x = .ok (some q)) : q = x := by
  unfold fromLimbsWithAll at h
  obtain ⟨s, hs, h⟩ := result_bind_ok_inv _ _ _ h
  obtain ⟨i, hi, h⟩ := result_bind_ok_inv _ _ _ h
  obtain ⟨bp, hbp, h⟩ := result_bind_ok_inv _ _ _ h
  rcases bp with ⟨b, i'⟩
  cases b <;> simp [Aeneas.Std.bind] at h
  exact h.symm

theorem checkedQWithAll_success_limbs (all : IterAll) (k : Qm) (q : Q)
    (h : checkedQWithAll all k = .ok (.Ok q)) :
    q = Array.make 4#usize [k.c0.a, k.c0.b, k.c1.a, k.c1.b] := by
  unfold checkedQWithAll at h
  obtain ⟨a, ha, h⟩ := result_bind_ok_inv _ _ _ h
  obtain ⟨o, ho, h⟩ := result_bind_ok_inv _ _ _ h
  have haValue : a = Array.make 4#usize [k.c0.a,k.c0.b,k.c1.a,k.c1.b] := by
    have h' : Result.ok a = Result.ok
      (Array.make 4#usize [k.c0.a,k.c0.b,k.c1.a,k.c1.b]) := by
      simpa [limbsOf] using ha.symm
    exact Result.ok.inj h'
  have hoSome : o = some q := by
    cases o with
    | none => simp [optionOkOr] at h
    | some q' =>
      simp [optionOkOr] at h
      exact congrArg Option.some h
  have hfrom : fromLimbsWithAll all a = .ok (some q) := by
    simpa [hoSome] using ho
  have hq := fromLimbsWithAll_success_identity all a q hfrom
  rw [haValue] at hq
  exact hq

#print axioms fromLimbsWithAll_success_identity
#print axioms checkedQWithAll_success_limbs
end AspisR1EbyKCheckedQAllParamV1
