import XSa_PartFold
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PartRun

theorem run {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat)
 (n : Nat) (i : Usize) (a b : Dot) (bound : i.val+n≤29) :
 XSa_DotRun.run sem s g point n i a b =
 (do let st ← XSa_OptionFold.run (XSa_PartFold.step sem s g point) (List.range' i.val n) (a,b)
     XSa_PartFold.finish st) := by
 induction n generalizing i a b with
 | zero => rfl
 | succ n ih =>
   have hi : i.val<29 := by omega
   have he : XRn_Join_usize i.val=i :=
     UScalar.eq_of_val_eq (XRy_ClaimSelect.usize_value i.val (by omega))
   simp only [XSa_DotRun.run,List.range'_succ,XSa_OptionFold.run,XSa_PartFold.step,bind_assoc_eq]
   rw [he]
   apply (bind_eq_iff _ _ _).mpr
   intro q hq
   by_cases hv : XSa_CheckedQ.valid q=true
   · simp only [hv,if_true,bind_assoc_eq,bind_tc_ok]
     apply (bind_eq_iff _ _ _).mpr
     intro v hval
     apply (bind_eq_iff _ _ _).mpr
     intro a' ha
     apply (bind_eq_iff _ _ _).mpr
     intro b' hb
     obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
     simp only [bind_tc_ok,ej]
     rw [ih j a' b' (by scalar_tac)]
     have hone : (1#usize).val=1 := by scalar_tac
     simp only [hj,hone]
   · simp only [hv,Bool.false_eq_true,if_false,bind_tc_ok,XSa_PartFold.finish]

#print axioms run
end XSa_PartRun
