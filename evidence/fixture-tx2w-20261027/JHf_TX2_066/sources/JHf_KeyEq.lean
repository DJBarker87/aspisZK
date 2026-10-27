import JHd_KeyStd
import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_KeyEq
open Aeneas Aeneas.Std Result

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
#print axioms lists

theorem key (left right : AdapterRw.solana_pubkey.Pubkey) :
    JHd_KeyStd.keyEq left right=Hist_Authority.keyEq left right := by
  classical
  unfold JHd_KeyStd.keyEq Hist_Authority.keyEq core.array.equality.PartialEqArray.eq
  rw [if_pos (left.property.trans right.property.symm)]
  rw [lists left.val right.val (left.property.trans right.property.symm)]
  congr 1
  simp only [Subtype.val_inj]
  by_cases h : left=right <;> simp [h]
#print axioms key
end AspisR1.JHf_KeyEq
end
