import Aeneas
/-! Symbolic sequencing: no arithmetic callee is unfolded. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBind51
open Aeneas Aeneas.Std Result

theorem three {Q : Type} (linear : Result (Q × Q))
    (horner : Q → Result Q) (finish : Q → Q → Result Q)
    (a b s z : Q) (hl : linear=ok (a,b)) (hs : horner a=ok s)
    (hz : finish s b=ok z) :
    (do let (a,b) ← linear; let s ← horner a; finish s b)=ok z := by
  rw [hl]
  simp only [bind_tc_ok]
  change (do let s ← horner a; finish s b)=ok z
  rw [hs]
  exact hz

#print axioms three
end R1Z.ProverCommitBind51
