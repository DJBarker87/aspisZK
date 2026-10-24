import Port3_WriterShape

/-! Coherence of checkpoint's canonical raw inventory with the very same
total numeric decoder used for query states. No completed model state is
chosen or postulated by these carrier identities. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_DecodeCoherence
open Aeneas Aeneas.Std
open CheckpointBytes3Namespaces
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

theorem k_decode (q : AspisR1Stage2.aspis_core.field.QM31)
    (h : Canonical (toK q)) :
    exactK (toK q) h = CheckpointBytes5Output.ofK q := by
  unfold exactK CheckpointBytes5Output.ofK
  congr 1
  funext j
  apply Fin.ext
  fin_cases j
  · simp [limbs,CheckpointBytes5Output.limb,toK,Nat.mod_eq_of_lt h.1]
  · simp [limbs,CheckpointBytes5Output.limb,toK,Nat.mod_eq_of_lt h.2.1]
  · simp [limbs,CheckpointBytes5Output.limb,toK,Nat.mod_eq_of_lt h.2.2.1]
  · simp [limbs,CheckpointBytes5Output.limb,toK,Nat.mod_eq_of_lt h.2.2.2]

theorem e_decode (q : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (h : CanonicalWide (toE q)) :
    exactE (toE q) h = CheckpointBytes5Output.ofE q := by
  change (⟨exactK (toK q.c0) h.1,exactK (toK q.c1) h.2⟩ : OraclePortCheckpointAbiC5.E) = _
  rw [k_decode,k_decode]
  rfl

#print axioms k_decode
#print axioms e_decode
end AspisR1.Port3_DecodeCoherence
end
