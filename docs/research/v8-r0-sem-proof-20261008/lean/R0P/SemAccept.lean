import R0P.SemD3

/-! Checks of the parsed semantic transcript imply the recursive sumcheck
acceptance predicate. All dimensions are symbolic; no transcript is reduced. -/
set_option autoImplicit false
noncomputable section
namespace R0P.Sumcheck
open Polynomial
variable {K : Type} [Field K]

/-- The nonempty boundary, chaining and terminal checks are exactly the
recursive sumcheck verifier. -/
theorem accept_of_checks (d n : Nat) (G : (Fin (n+1) → K) → K) (c : K)
    (polys : Fin (n+1) → K[X]) (α : Fin (n+1) → K)
    (hdeg : ∀ j, (polys j).natDegree ≤ d)
    (hfirst : (polys 0).eval 0 + (polys 0).eval 1 = c)
    (hchain : ∀ j : Fin n, (polys j.succ).eval 0 + (polys j.succ).eval 1 =
      (polys j.castSucc).eval (α j.castSucc))
    (hlast : (polys (Fin.last n)).eval (α (Fin.last n)) = G α) :
    accept d (n+1) G c polys α := by
  induction n generalizing c with
  | zero =>
      refine ⟨hdeg 0, hfirst, ?_⟩
      change G (Fin.cons (α 0) (fun i => i.elim0)) = (polys 0).eval (α 0)
      have htail : (fun i : Fin 0 => i.elim0) = Fin.tail α := by
        funext i; exact i.elim0
      rw [htail, Fin.cons_self_tail]
      exact hlast.symm
  | succ n ih =>
      refine ⟨hdeg 0, hfirst, ?_⟩
      apply ih
      · intro j; exact hdeg j.succ
      · exact hchain 0
      · intro j; exact hchain j.succ
      · simpa only [Fin.tail, Fin.succ_last, Fin.cons_self_tail] using hlast

#print axioms accept_of_checks
end R0P.Sumcheck

namespace R0P.SemSource
open Polynomial Sumcheck
variable {K : Type} [Field K]

/-- The parsed ten-round checks discharge G14's acceptance bridge. -/
theorem checksAccept (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (t : Trace K) : ChecksAccept pub B t := by
  intro r polys h
  have hα (j : Fin 10) : semSlice r 14 10 j = r ⟨14 + j.val, by omega⟩ := by
    simp only [semSlice, semPrefixVal, dif_pos (show 14 + j.val < 24 by omega)]
  have hαf : (fun j : Fin 10 => r ⟨14 + j.val, by omega⟩) = semSlice r 14 10 :=
    (funext hα).symm
  have hzc : semSlice r 3 10 = (fun j : Fin 10 => r ⟨3 + j.val, by omega⟩) := by
    funext j
    simp only [semSlice, semPrefixVal, dif_pos (show 3 + j.val < 24 by omega)]
  simp only [sumcheckChecks, List.getElem_ofFn] at h
  refine accept_of_checks 27 9 _ 0 polys (semSlice r 14 10) h.1 h.2.1 ?_ ?_
  · intro j
    simpa only [hα] using h.2.2.1 j
  · convert h.2.2.2 using 1 <;>
      simp only [virtualPoly, preZc_semSlice, semSlice_zero_apply, hαf, hzc, hα] <;> rfl

#print axioms checksAccept
end R0P.SemSource
end
