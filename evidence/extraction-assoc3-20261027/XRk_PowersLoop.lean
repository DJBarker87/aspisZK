import XRk_Funs
import XRk_PowersArray
import XRk_LoopStep
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools XRk_PowersArray
namespace XRk_PowersLoop
abbrev E := aspis_core.field.wide_exact.WideExact
def chosen {N : Usize} (r : Array E N × Option (Array E N)) : Array E N := r.2.getD r.1

theorem suffix {N : Usize} (x : E) (a : Array E N) (p : E) (i : Usize)
    (r : Array E N × Option (Array E N)) (bound : i.val ≤ N.val)
    (run : weights.powers_loop x a p i = ok r) :
    ∃ rest, XRk_powers x (N.val-i.val) p = ok rest ∧
      (chosen r).val = a.val.take i.val ++ rest := by
  suffices ∀ n (a : Array E N) p i r, N.val-i.val=n → i.val≤N.val →
      weights.powers_loop x a p i=ok r →
      ∃ rest,XRk_powers x (N.val-i.val) p=ok rest ∧
        (chosen r).val=a.val.take i.val++rest from
    this (N.val-i.val) a p i r rfl bound run
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a p i r measure bound run
    unfold weights.powers_loop at run
    obtain ⟨step,hbody,run⟩ := XRk_LoopStep.unroll _ _ _ run
    dsimp only at hbody
    unfold weights.powers_loop.body at hbody
    split at hbody
    · rename_i more
      obtain ⟨⟨old,back⟩,hindex,hbody⟩ := bind_success _ _ _ hbody
      obtain ⟨next,hadd,hbody⟩ := bind_success _ _ _ hbody
      have hi : i.val < a.val.length := by rw [a.property]; scalar_tac
      have inc := add_one_value i N next (by scalar_tac) hadd
      have written := write_prefix a i old back hindex hi p
      split at hbody
      · rename_i atEnd
        have same := Result.ok.inj hbody
        subst step
        simp only [bind_tc_ok] at run
        have same := Result.ok.inj run
        subst r
        have size : i.val+1=N.val := by simpa only [atEnd] using inc.symm
        have remaining : N.val-i.val=1 := by omega
        refine ⟨[p],?_,?_⟩
        · simp only [remaining,XRk_powers]
        · simpa only [chosen,Option.getD_some,size,←(back p).property,List.take_length] using written
      · rename_i notEnd
        obtain ⟨q,hmul,hbody⟩ := bind_success _ _ _ hbody
        have same := Result.ok.inj hbody
        subst step
        simp only [bind_tc_ok] at run
        have ne : next.val ≠ N.val := by intro eq; apply notEnd; scalar_tac
        have nb : next.val ≤ N.val := by scalar_tac
        obtain ⟨tail,htail,hresult⟩ := ih (N.val-next.val) (by omega)
          (back p) q next r rfl nb run
        have remaining : N.val-i.val = (N.val-next.val)+1 := by omega
        have positive : 0<N.val-next.val := by omega
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        refine ⟨p::tail,?_,?_⟩
        · rw [remaining,hk,XRk_powers,hmul,bind_tc_ok]
          have hr : XRk_powers x (k+1) q = ok tail := by simpa only [hk] using htail
          rw [hr,bind_tc_ok]
        · rw [hresult,inc,written,List.append_assoc]
          rfl
    · rename_i noMore
      have same := Result.ok.inj hbody
      subst step
      simp only [bind_tc_ok] at run
      have same := Result.ok.inj run
      subst r
      have size : i.val=N.val := by scalar_tac
      refine ⟨[],?_,?_⟩
      · simp only [size,Nat.sub_self,XRk_powers]
      · simp only [chosen,Option.getD_none,size,←a.property,List.take_length,List.append_nil]
#print axioms suffix
end XRk_PowersLoop
