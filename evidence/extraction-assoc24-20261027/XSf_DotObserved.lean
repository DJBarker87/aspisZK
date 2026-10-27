import XSf_ByteDomain
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRk_ResultTools XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSf_DotObserved

theorem reads {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point n : Nat)
 (i : Usize) (a b : Dot) (out : C.E) (bound : i.val+n≤29)
 (run : XSa_DotRun.run sem s g point n i a b=ok (some out)) :
 ∀ j : Nat, j<n → ∃ q : E.Q,
 XRy_ClaimSelect.read (es sem) s point (i.val+j)=ok q ∧ XSa_CheckedQ.valid q=true := by
 induction n generalizing i a b with
 | zero => intro j hj; omega
 | succ n ih =>
   simp only [XSa_DotRun.run] at run
   obtain ⟨q,hq,run⟩ := bind_success _ _ _ run
   by_cases hv : XSa_CheckedQ.valid q=true
   · simp only [hv,if_true] at run
     obtain ⟨v,hvread,run⟩ := bind_success _ _ _ run
     obtain ⟨a',ha,run⟩ := bind_success _ _ _ run
     obtain ⟨b',hb,run⟩ := bind_success _ _ _ run
     obtain ⟨next,hn,run⟩ := bind_success _ _ _ run
     obtain ⟨next',hn',hval⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
     have he : next=next' := Result.ok.inj (hn.symm.trans hn')
     subst next
     have value : next'.val=i.val+1 := by scalar_tac
     intro j hj
     cases j with
     | zero => exact ⟨q,by simpa only [Nat.add_zero] using hq,hv⟩
     | succ j =>
       obtain ⟨q',hr,hc⟩ := ih next' a' b' (by omega) run j (by omega)
       refine ⟨q',?_,hc⟩
       have index : i.val+(j+1)=next'.val+j := by omega
       simpa only [index] using hr
   · simp only [hv,Bool.false_eq_true,if_false] at run
     cases run

#print axioms reads
end XSf_DotObserved
