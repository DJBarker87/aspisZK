import LoopPowersCandidatePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1LoopPowers

theorem loop_total_exact {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hx : Canonical x) (hi : i.val ≤ N.val) (hp : Canonical p)
    (hpower : decode p = decode x ^ i.val) (hprefix : Prefix x a i.val) :
    ∃ out, weights.powers_loop x a p i = .ok out ∧ Prefix x out N.val := by
  have hwp : WP.spec (weights.powers_loop x a p i) (fun out => Prefix x out N.val) := by
    unfold weights.powers_loop
    refine loop.spec_decr_nat
      (fun s : Array field.WideExact N × field.WideExact × Usize => N.val-s.2.2.val)
      (fun s : Array field.WideExact N × field.WideExact × Usize =>
        s.2.2.val ≤ N.val ∧ Canonical s.2.1 ∧ decode s.2.1 = decode x ^ s.2.2.val ∧ Prefix x s.1 s.2.2.val)
      (fun out => Prefix x out N.val)
      (fun s : Array field.WideExact N × field.WideExact × Usize =>
        weights.powers_loop.body x s.1 s.2.1 s.2.2)
      (a,p,i) ?_ ?_
    · intro state hs
      rcases state with ⟨arr,pow,idx⟩
      rcases hs with ⟨hile,hcanon,he,hpre⟩
      change idx.val ≤ N.val at hile
      by_cases hlt : idx.val < N.val
      · obtain ⟨pow',idx',hb,hcanon',hm,hidx⟩ := loop_body_step x pow arr idx hlt hx hcanon
        rw [hb,WP.spec_ok]
        change (idx'.val ≤ N.val ∧ Canonical pow' ∧ decode pow' = decode x ^ idx'.val ∧
          Prefix x (arr.set idx pow) idx'.val) ∧ N.val-idx'.val < N.val-idx.val
        constructor
        · refine ⟨by omega,hcanon',?_,?_⟩
          · rw [hidx,hm,he,pow_succ]
          · rw [hidx]
            exact prefix_set x pow arr idx hlt hcanon he hpre
        · omega
      · have hge : N.val ≤ idx.val := Nat.le_of_not_gt hlt
        have hb := loop_body_done x pow arr idx hge
        rw [hb,WP.spec_ok]
        have heq : idx.val=N.val := by omega
        simpa only [heq] using hpre
    · exact ⟨hi,hp,hpower,hprefix⟩
  obtain ⟨out,hout,hpre⟩ := WP.spec_imp_exists hwp
  exact ⟨out,hout,hpre⟩

theorem powers_total_exact (N : Usize) (x : field.WideExact) (hx : Canonical x) :
    ∃ out, weights.powers N x = .ok out ∧
      ∀ j : Fin N.val,
        Canonical (out.val[j.val]'(by rw [out.property]; exact j.isLt)) ∧
        decode (out.val[j.val]'(by rw [out.property]; exact j.isLt)) = decode x ^ j.val := by
  obtain ⟨out,hout,hpre⟩ := loop_total_exact x field.WideExact.ONE
    (Array.repeat N field.WideExact.ONE) 0#usize hx (by scalar_tac) one_canonical
    (by simpa using one_decode) (by
      intro j hj
      change j.val < 0 at hj
      exact (Nat.not_lt_zero _ hj).elim)
  refine ⟨out,?_,?_⟩
  · exact hout
  · intro j
    exact hpre j j.isLt

#print axioms loop_total_exact
#print axioms powers_total_exact
end AspisR1LoopPowers
