import CheckpointBytes5Output
import CheckpointBytes3Namespaces
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterNumeric
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
open CheckpointBytes3Namespaces

theorem exact_k (q : RawK) (canonical : Canonical q) :
    exactK q canonical=CheckpointBytes5Output.ofK (fromK q) := by
  apply congrArg RetainedFieldByteCodec.qm31ExactLimbEquiv
  funext j
  apply Fin.ext
  fin_cases j <;>
    simp only [limbs,CheckpointBytes5Output.limb,fromK,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals exact (Nat.mod_eq_of_lt (by rcases canonical with ⟨h0,h1,h2,h3⟩;assumption)).symm

theorem exact_e (q : CheckpointBytesE.RawE) (canonical : CanonicalWide q) :
    exactE q canonical=CheckpointBytes5Output.ofE (fromE q) := by
  change (⟨exactK q.c0 canonical.1,exactK q.c1 canonical.2⟩ : OraclePortCheckpointAbiC5.E)=_
  rw [exact_k,exact_k]
  rfl

#print axioms exact_k
#print axioms exact_e
end AspisR1.F3L_WriterNumeric
end
