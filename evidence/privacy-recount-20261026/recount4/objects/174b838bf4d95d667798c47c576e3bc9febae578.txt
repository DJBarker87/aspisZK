import R1Z.ProverRwQueryWindow
set_option autoImplicit false
namespace R1Z.ProverRwQueryWindowStop
open Aeneas Aeneas.Std Result ProverRwQueryTransition ProverRwQueryWindow
open Query31ExplicitScanBody

theorem stop_lt (word : Nat → U32) (fuel i : Nat) (s sf : CurrentScan)
    (hlen : s.accepted_len.val≤22) (bound : s.draws.val+fuel≤64)
    (hr : window word fuel i s=ok (true,sf)) :
    sf.draws.val<s.draws.val+fuel := by
  induction fuel generalizing i s with
  | zero =>
    have he := congrArg Prod.fst (Result.ok.inj hr)
    cases he
  | succ fuel ih =>
    by_cases full : s.accepted_len=22#usize
    · simp only [window,full,if_true,Result.ok.injEq,Prod.mk.injEq,true_and] at hr
      subst sf; omega
    · by_cases cap : s.draws=64#usize
      · simp only [window,full,if_false,cap,if_true,Result.ok.injEq,Prod.mk.injEq,true_and] at hr
        subst sf; omega
      · have active : s.accepted_len.val<22 := by
          have ne : s.accepted_len.val≠22 := by intro he; apply full; exact UScalar.eq_of_val_eq he
          omega
        obtain ⟨next,hn,hnlen,hndraw,_⟩ := advance_q22 s (word i) active (by omega)
        simp only [window,full,cap,if_false,hn,bind_tc_ok] at hr
        have ht := ih (i+1) next hnlen (by omega) hr
        omega

#print axioms stop_lt
end R1Z.ProverRwQueryWindowStop
