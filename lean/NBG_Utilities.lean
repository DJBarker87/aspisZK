import Aeneas
set_option autoImplicit false
noncomputable section
namespace NBG_Utilities
open Aeneas Aeneas.Std Result
def pack {α : Type} (a b c d e f g h : α) : Array α 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]

theorem shape {α : Type} (a : Array α 8#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, a=pack a0 a1 a2 a3 a4 a5 a6 a7 := by
  rcases a with ⟨xs,h⟩
  change xs.length=8 at h
  cases xs with
  | nil => simp at h
  | cons a0 xs =>
    cases xs with
    | nil => simp at h
    | cons a1 xs =>
      cases xs with
      | nil => simp at h
      | cons a2 xs =>
        cases xs with
        | nil => simp at h
        | cons a3 xs =>
          cases xs with
          | nil => simp at h
          | cons a4 xs =>
            cases xs with
            | nil => simp at h
            | cons a5 xs =>
              cases xs with
              | nil => simp at h
              | cons a6 xs =>
                cases xs with
                | nil => simp at h
                | cons a7 xs =>
                  cases xs with
                  | nil => exact ⟨a0,a1,a2,a3,a4,a5,a6,a7,rfl⟩
                  | cons a8 xs => simp at h

theorem lists (xs ys : List U8) (width : xs.length=ys.length) :
    List.allM (fun (x,y) => do let b ← core.cmp.PartialEqU8.ne x y;ok (¬ b))
      (xs.zip ys)=ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil=>rfl
    | cons y ys=>simp only [List.length_nil,List.length_cons] at width;omega
  | cons x xs ih =>
    cases ys with
    | nil=>simp only [List.length_nil,List.length_cons] at width;omega
    | cons y ys=>
      have tail : xs.length=ys.length := Nat.succ.inj width
      by_cases same : x=y
      · subst y
        have comp : core.cmp.impls.PartialEqU8.ne x x=false := by
          simp [core.cmp.impls.PartialEqU8.ne]
        simp only [List.zip_cons_cons,List.allM,comp,bind_tc_ok]
        change List.allM _ (xs.zip ys)=ok (decide (x::xs=x::ys))
        simpa only [List.cons.injEq,true_and,liftFun2,bind_tc_ok] using ih ys tail
      · have comp : core.cmp.impls.PartialEqU8.ne x y=true := by
          simp [core.cmp.impls.PartialEqU8.ne,same]
        simp only [List.zip_cons_cons,List.allM,comp,bind_tc_ok]
        change ok false=ok (decide (x::xs=y::ys))
        simp [same]

#print axioms shape
#print axioms lists
end NBG_Utilities
