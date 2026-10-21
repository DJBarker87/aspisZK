import R1Z.ProverCommitProductOracle25
/-! Exact nominal joins to the existing SecP and 24-by-5 fuel carrier.
Only finite coordinate reassociation is used; no new randomness is sampled. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitProductCarrier25
open R0Z R0Z.FsStatement R0Z.FsAbort R1Z.CouplingR1PBin
open ProverCommitStreamPack25 ProverCommitProductOracle25
attribute [local instance] Classical.propDecidable

def trioEquiv (X : Type) : (Fin 3 → X) ≃ Trio X where
  toFun f := (f 0,f 1,f 2)
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 (Fin.cons p.2.2 (fun i => i.elim0)))
  left_inv f := by funext i;fin_cases i <;> rfl
  right_inv _ := rfl

def coordinates : (Fin 8 × Fin 3) ≃ Fin 24 := finProdFinEquiv

def attemptsEquiv (X : Type) : (Fin 24 → X) ≃ (Fin 8 → Fin 3 → X) where
  toFun f a j := f (coordinates (a,j))
  invFun f i := f (coordinates.symm i).1 (coordinates.symm i).2
  left_inv f := by funext i;dsimp only
                   rw [Prod.mk.eta,Equiv.apply_symm_apply]
  right_inv f := by funext a j;dsimp only;rw [Equiv.symm_apply_apply]

def fuelEquiv : ProverCommitFuelJoin22.Tape ≃ (Fin 8 → Trio (Fin 5 → OracleAnswer)) :=
  (attemptsEquiv (Fin 5 → OracleAnswer)).trans (Equiv.piCongrRight fun _ => trioEquiv _)

def secretEquiv : (Fin 8 → GamesR1PBin.SecP) ≃
    (Fin 8 → Trio GamesR1PBin.NZ) := Equiv.piCongrRight fun _ => trioEquiv _

def inputEquiv : ((Fin 8 → GamesR1PBin.SecP) × ProverCommitFuelJoin22.Tape) ≃ Input :=
  (Equiv.prodCongr secretEquiv fuelEquiv).trans
    { toFun p a := (p.1 a,p.2 a)
      invFun p := ((fun a => (p a).1),(fun a => (p a).2))
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The exact pre-existing model secret/fuel carrier gives the uniform source
stream proved above; no deterministic fuel factor or changed secret domain. -/
theorem source_words_uniform : MP (fun p => words (inputEquiv p)) := by
  intro test
  exact (mp_equiv inputEquiv (fun p => test (words p))).trans
    ((QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
      ((words_uniform test).trans (QueryScanIdealHistory.mean_fintype_transport _ _ _)))

#print axioms source_words_uniform
end R1Z.ProverCommitProductCarrier25
