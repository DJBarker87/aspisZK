import JHd_KeyStd
import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_KeyEq
open Aeneas Aeneas.Std Result

theorem lists (xs ys : List U8) (width : xs.length=ys.length) :
    List.allM (fun (x,y) => do let b ← core.cmp.PartialEqU8.ne x y;ok (!b))
      (xs.zip ys)=ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil=>simp_all
    | cons y ys=>
      have tail : xs.length=ys.length := Nat.succ.inj width
      simp only [List.zip_cons_cons,List.allM]
      by_cases same : x=y
      · subst y
        simp only [core.cmp.PartialEqU8,core.cmp.PartialEq.ne.default,bind_tc_ok,
          bne_self_eq_false,Bool.not_false,↓reduceIte,List.cons.injEq,true_and]
        exact ih ys tail
      · have comp : core.cmp.PartialEqU8.ne x y=ok true := by
          simp [core.cmp.PartialEqU8,core.cmp.PartialEq.ne.default,same]
        simp only [comp,bind_tc_ok,Bool.not_true,Bool.false_eq_true,↓reduceIte]
        simp [same]
#print axioms lists

theorem key (left right : AdapterRw.solana_pubkey.Pubkey) :
    JHd_KeyStd.keyEq left right=Hist_Authority.keyEq left right := by
  classical
  unfold JHd_KeyStd.keyEq Hist_Authority.keyEq core.array.equality.PartialEqArray.eq
  rw [if_pos (left.property.trans right.property.symm)]
  rw [lists left.val right.val (left.property.trans right.property.symm)]
  congr 1
  exact propext Subtype.val_inj
#print axioms key
end AspisR1.JHf_KeyEq
end
