import R1Z.ProverCommitSourceExhaustion

/-! A typed source equation suffices for the fibre, exhaustion and numerical
premises together. This interface is not a certificate of a Rust caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCallerInstance
open R0P R0Z.FsStatement R0Z.JointView R1Z.GamesR1 R1Z.GamesR1PBin R1Z.FinalR1PBin
  R1Z.ProverCommitTapeCompletion R1Z.ProverCommitSourceDecoder
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => R1Z.ProverCommitWordCarrier.sourceBase (K := K)
variable {W : R1Wire K CommitHandle Aux}

def blockTransport {n m : Nat} (eq : n = m) :
    (Fin n → OracleAnswer) ≃ (Fin m → OracleAnswer) :=
  Equiv.arrowCongr (finCongr eq) (Equiv.refl OracleAnswer)

def inputsTransport (Pr : R1ProverP K CommitHandle Aux F W)
    (h₁ : Pr.E₁ = E₁) (h₂ : Pr.E₂ = E₂) :
    ((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) ≃ Inputs :=
  Equiv.prodCongr (blockTransport h₁) (blockTransport h₂)

structure CallerLaw (Pr : R1ProverP K CommitHandle Aux F W) : Prop where
  blocks₁ : Pr.E₁ = E₁
  blocks₂ : Pr.E₂ = E₂
  quotient : ∃ coordinates : SourceTape K F ≃ SourceTape K F, ∀ e,
    quotientDecode (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) => Pr.tapeOf e.1 e.2) e =
      (quotientDecoder (inputsTransport Pr blocks₁ blocks₂ e)).map coordinates

attribute [local irreducible] E₁ E₂ L₁ L₂

theorem fibres (Pr : R1ProverP K CommitHandle Aux F W) (law : CallerLaw Pr)
    (s : SourceTape K F) :
    (Finset.univ.filter (fun e => quotientDecode (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) => Pr.tapeOf e.1 e.2) e = some s)).card =
      quotientFibreSize := by
  let eqv := inputsTransport Pr law.blocks₁ law.blocks₂
  obtain ⟨coordinates, caller⟩ := law.quotient
  calc
    _ = (Finset.univ.filter (fun e : Inputs => quotientDecoder e = some (coordinates.symm s))).card := by
      apply Finset.card_bij (fun e _ => eqv e)
      · intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (map_equiv_some coordinates _ s).mp ((caller e).symm.trans (Finset.mem_filter.mp he).2)⟩
      · intro a _ b _ h; exact eqv.injective h
      · intro e he
        refine ⟨eqv.symm e, ?_, eqv.apply_symm_apply e⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [caller, eqv.apply_symm_apply]
        exact (map_equiv_some coordinates _ s).mpr (Finset.mem_filter.mp he).2
    _ = _ := by
      convert R1Z.ProverCommitSourceDecoder.quotient_equal_fibres (K := K) (coordinates.symm s) using 1
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem exhausted_transport {n m : Nat} (eq : n = m)
    (e : Fin n → OracleAnswer) (L : Nat) :
    R1Z.CommitReadsR1.Exhausted (wordsE m (blockTransport eq e)) L ↔
      R1Z.CommitReadsR1.Exhausted (wordsE n e) L := by
  cases eq
  rfl

theorem exhaustion (Pr : R1ProverP K CommitHandle Aux F W) (law : CallerLaw Pr) :
    RExh Pr L₁ L₂ := by
  intro e₁ e₂ hnone
  obtain ⟨coordinates, caller⟩ := law.quotient
  have hm : (quotientDecoder (K := K) (inputsTransport Pr law.blocks₁ law.blocks₂ (e₁,e₂))).map coordinates = none := by
    rw [← caller]
    simp only [quotientDecode, hnone, Option.map_none]
  have hq : quotientDecoder (K := K) (inputsTransport Pr law.blocks₁ law.blocks₂ (e₁,e₂)) = none := by
    cases hd : quotientDecoder (K := K) (inputsTransport Pr law.blocks₁ law.blocks₂ (e₁,e₂)) with
    | none => rfl
    | some v => simp only [hd, Option.map_some, reduceCtorEq] at hm
  have h := (quotient_exhausted _).mp hq
  exact h.imp ((exhausted_transport law.blocks₁ e₁ L₁).mp)
    ((exhausted_transport law.blocks₂ e₂ L₂).mp)

theorem budgets (Pr : R1ProverP K CommitHandle Aux F W) (law : CallerLaw Pr) :
    Pr.E₁ ≤ 2^64 ∧ Pr.E₂ ≤ 2^64 ∧
    16*L₁ ≤ Pr.E₁*8 ∧ 16*L₂ ≤ Pr.E₂*8 ∧
    R1Z.CommitReadsR1.RCommitCount L₁ L₂ ∧
    Pr.E₁ ≤ 2*L₁ ∧ Pr.E₂ ≤ 2*L₂ := by
  rw [law.blocks₁, law.blocks₂]
  exact ⟨source_budgets.2.2.2.2.1, source_budgets.2.2.2.2.2,
    source_budgets.1, source_budgets.2.1, source_counts,
    source_budgets.2.2.1, source_budgets.2.2.2.1⟩

#print axioms blockTransport
#print axioms inputsTransport
#print axioms fibres
#print axioms exhausted_transport
#print axioms exhaustion
#print axioms budgets
end R1Z.ProverCommitCallerInstance
