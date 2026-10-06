import R0FS.Hypotheses

/-! # The generic theorem applied to R0

`FS.theorem4` with the R0 protocol object, its §6 state function and the
proved (D1)–(D3) and verifier property.  Remaining hypotheses: the sampler
laws (`SamplerLaws`), (INJ) (`FS.Inj`) and the `Q_tot` bound. -/
set_option autoImplicit false
namespace R0FS

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
noncomputable section

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}
variable {Pf I B : Type} {Kw : Nat} [DecidableEq I] [Fintype I] [Fintype B] [Nonempty B]

theorem r0_fiat_shamir (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p)
    (P : Program I (Block B Kw) Pf) (x : Stmt E Sfield) (κ : Nat → ℚ) (Qtot : Nat)
    (inj : Inj (protocol p) P (verifierR0 p) x κ Qtot)
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P (verifierR0 p) x)) ≤ Qtot) :
    mean (fun H : I → Block B Kw =>
        indicator (accepts (eval H (experiment P (verifierR0 p) x)) ∧
          extractFails (protocol p) x (eval H (experiment P (verifierR0 p) x)))) ≤
      (Qtot : ℚ) * maxErr (ε E) 5 + κ Qtot :=
  theorem4 (protocol p) (roundByRound p) P (verifierR0 p) x κ Qtot
    (d1 p) (d2 p hs) (d3 p hs) (readsChallenges p) inj hQ

end

/-- The protocol field 𝔼 = `WideExact`, |𝔼| = P^8. -/
theorem wide_r0_fiat_shamir :
    type_of% (@r0_fiat_shamir AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @r0_fiat_shamir AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms r0_fiat_shamir
#print axioms wide_r0_fiat_shamir
#print axioms d1
#print axioms d2
#print axioms d3
#print axioms readsChallenges
end R0FS
