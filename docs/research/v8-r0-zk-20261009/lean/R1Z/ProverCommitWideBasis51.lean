import R1Z.ProverCommitQBasis51
import R1Z.PrivacyR1AcctBasis
/-! Native QM31 basis maps to the existing exact WideExact payload basis. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWideBasis51
open AspisV8R15.ExactTowerBase
abbrev K := AspisWideTower.WideExact
abbrev F := PrivacyR1AcctBasis.F
abbrev basis := PrivacyR1AcctBasis.basis

def embed : QM31Exact →+* K := algebraMap QM31Exact K

theorem basis_i : embed ProverCommitQBasis51.basis.i=basis.i := by rfl
theorem basis_u : embed ProverCommitQBasis51.basis.u=basis.u := by rfl

#print axioms basis_i
#print axioms basis_u
end R1Z.ProverCommitWideBasis51
