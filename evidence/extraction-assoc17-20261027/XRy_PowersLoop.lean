import XRy_PowersStep
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XRy_LoopWide
set_option autoImplicit false
namespace XRy_PowersLoop

theorem done {S O : Type} (body : S → Result (ControlFlow S O)) (s : S) (out : O)
 (h : body s=ok (.done out)) : loop body s=ok out := by rw [loop.eq_def,h]

theorem cont {S O : Type} (body : S → Result (ControlFlow S O)) (s next : S)
 (h : body s=ok (.cont next)) : loop body s=loop body next := by rw [loop.eq_def,h]

theorem paired (fuel : Nat) {N : Usize} (x : C.E) (hx : XRy_WideMultiply.Canonical x)
 (a : Array C.E N) (p : C.E) (hp : XRy_WideMultiply.Canonical p)
 (i : Usize) (hi : i.val≤N.val) (remaining : N.val-i.val≤fuel) :
 ∃ out pending,
 XRn_Join_Release.weights.powers_loop x a p i = ok (out,pending) ∧
 (pending=none ∨ pending=some out) ∧
 AspisR1LoopPowers.weights.early_powers_loop (toLoop x) (arr toLoop a) (toLoop p) i =
   ok (arr toLoop out) := by
 induction fuel generalizing a p i with
 | zero =>
   have hn : ¬i<N := by scalar_tac
   refine ⟨a,none,?_,Or.inl rfl,?_⟩
   · apply done
     simp only [XRn_Join_Release.weights.powers_loop.body,if_neg hn]
   · apply done
     simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_neg hn]
 | succ n ih =>
   by_cases hlt : i.val<N.val
   · obtain ⟨i',vi,cases⟩ := XRy_PowersStep.step x p a i hlt hx hp
     rcases cases with ⟨he,er,et⟩ | ⟨he,p',hp',er,et⟩
     · refine ⟨a.set i p,some (a.set i p),?_,Or.inr rfl,?_⟩
       · exact done _ _ _ er
       · exact done _ _ _ et
     · obtain ⟨out,pending,hr,hpending,ht⟩ := ih (a.set i p) p' hp' i' (by omega) (by omega)
       refine ⟨out,pending,?_,hpending,?_⟩
       · exact (cont _ _ _ er).trans hr
       · exact (cont _ _ _ et).trans ht
   · have hn : ¬i<N := by scalar_tac
     refine ⟨a,none,?_,Or.inl rfl,?_⟩
     · apply done
       simp only [XRn_Join_Release.weights.powers_loop.body,if_neg hn]
     · apply done
       simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_neg hn]

#print axioms done
#print axioms cont
#print axioms paired
end XRy_PowersLoop
