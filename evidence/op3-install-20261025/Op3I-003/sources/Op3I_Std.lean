import Op3I_Source
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace Op3I_Std

def eqList {T U : Type} (cmp : core.cmp.PartialEq T U) : List T → List U → Result Bool
  | [], [] => ok true
  | x::xs, y::ys => do
      let b ← cmp.eq x y
      if b then eqList cmp xs ys else ok false
  | _, _ => ok false

def anyList {T F : Type} (f : core.ops.function.FnMut F T Bool) :
    List T → F → Result (Bool × Nat)
  | [], _ => ok (false,0)
  | x::xs, state => do
      let (b,state') ← f.call_mut state x
      if b then ok (true,1) else do
        let (b,n) ← anyList f xs state'
        ok (b,n+1)
termination_by xs _ => xs.length

def ops : Op3I_Source.ParseShapeOps where
  sliceEq := fun cmp s a => eqList cmp s.val a.val
  sliceNe := fun cmp s a => do
    let b ← eqList cmp s.val a.val
    ok (!b)
  iterAny := fun f it state => do
    let (b,n) ← anyList f (it.slice.val.drop it.i) state
    ok (b,{it with i := it.i+n})

theorem eqList_u8 (xs ys : List U8) :
    eqList core.cmp.PartialEqU8 xs ys = ok (decide (xs = ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eqList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eqList]
    | cons y ys =>
      simp only [eqList,core.cmp.PartialEqU8]
      by_cases h : x = y
      · subst y
        simpa using ih ys
      · simp [h]

#print axioms eqList_u8
end Op3I_Std
end
