import PV_L2E_LawPermutation
import R1Z.CouplingR1PBin
set_option autoImplicit false
noncomputable section
namespace PV_L2E_TriangularLaw
open R0Z PV_L2E_LawPermutation R1Z.CouplingR1PBin

theorem uniform {C R : Type} [Fintype C] [Fintype R]
    (e : C → R ≃ R) (test : C × R → ℚ) :
    mean (fun p => test (triangular e p))=mean test := mp_equiv (triangular e) test

/-- No rejected prefix or eager unused coin is resampled by this operation.
The observation may inspect the entire original coin vector. -/
theorem joint {C R O V : Type} [Fintype C] [Fintype R]
    (e : C → R ≃ R) (coinObservation : C → O) (sim : C → R → V)
    (test : O × V → ℚ) :
    mean (fun p : C × R => test (coinObservation p.1,sim p.1 (e p.1 p.2))) =
      mean (fun p : C × R => test (coinObservation p.1,sim p.1 p.2)) :=
  uniform e (fun p => test (coinObservation p.1,sim p.1 p.2))

#print axioms uniform
#print axioms joint
end PV_L2E_TriangularLaw
