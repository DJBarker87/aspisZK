import CompPolyFactorRecursion
import AspisV8R19.AdaptiveFirstReadLaw

namespace AspisR1.CompPolyFactorOracleProgram
open CompPoly AspisR1.CompPolySplitRetries AspisR1.CompPolyFactorRecursion
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Reuses the existing causal oracle-program semantics. Each answer is a
whole bounded retry tape; the input address is the factorizer's heap node. -/
def factorProgram {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (q t : Nat) : Nat → Nat → CPolynomial K →
      Program Nat (Fin t → K × K) (Option (List K))
  | 0, _, _ => .done none
  | fuel+1, node, f =>
      if f.natDegree = 0 then .done (some []) else
      if f.natDegree = 1 then .done (some [-f.coeff 0]) else
      .ask node (fun tape =>
        match retry f q t tape with
        | none => .done none
        | some d =>
          bind (factorProgram q t fuel (2*node+1) d) (fun left =>
            match left with
            | none => .done none
            | some l =>
              bind (factorProgram q t fuel (2*node+2) (f.divByMonic d)) (fun right =>
                match right with
                | none => .done none
                | some r => .done (some (l++r)))))

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

theorem factorProgram_eval (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) :
    (AspisV8R19.MemoizedProgramLaw.eval coins (factorProgram q t fuel node f)).2 =
      factor q t coins fuel node f := by
  induction fuel generalizing node f with
  | zero => rfl
  | succ fuel ih =>
    rw [factorProgram, factor]
    split
    · rfl
    · split
      · rfl
      · simp only [AspisV8R19.MemoizedProgramLaw.eval]
        cases hd : retry f q t (coins node) with
        | none => rfl
        | some d =>
          rw [eval_bind]
          dsimp only
          rw [ih]
          cases hl : factor q t coins fuel (2*node+1) d with
          | none => rfl
          | some l =>
            rw [eval_bind]
            dsimp only
            rw [ih]
            cases hr : factor q t coins fuel (2*node+2) (f.divByMonic d) <;> rfl

#print axioms factorProgram_eval
end AspisR1.CompPolyFactorOracleProgram
