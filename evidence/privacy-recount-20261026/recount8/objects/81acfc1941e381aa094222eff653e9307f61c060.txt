import R1Z.ProverCommitCompletionAdapter
import R1Z.CouplingR1P2Bin

/-! Quotient rejection law and independent spare completion. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView R0Z.FsAbortBounds R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
variable {Input K : Type} [Field K] [Fintype K] {F : Subfield K}
  [Fintype Input] [Nonempty Input]
instance : Nonempty (SourceTape K F) := ⟨(0, 0)⟩
instance : Nonempty (Padding K F) := ⟨0⟩

def quotientDecode (decode : Input → Option (Tape K F)) : Input → Option (SourceTape K F) :=
  fun i => (decode i).map project

def completeOrSpare (decode : Input → Option (Tape K F)) (p : Input × Tape K F) : Tape K F :=
  complete ((quotientDecode decode p.1).getD (project p.2)) (padding p.2)

def spareEquiv : (Input × Tape K F) ≃ (Input × SourceTape K F) × Padding K F :=
  (Equiv.prodCongr (Equiv.refl Input) completionEquiv.symm).trans (Equiv.prodAssoc _ _ _).symm

theorem mp_completeOrSpare (decode : Input → Option (Tape K F)) (c : ℕ)
    (hfib : ∀ s, (Finset.univ.filter (fun i => quotientDecode decode i = some s)).card = c) :
    MP (completeOrSpare decode) := by
  have hd : MP (fun p : Input × SourceTape K F => (quotientDecode decode p.1).getD p.2) :=
    fun f => R0Z.FsAbortTape.mean_decodeOrSpare _ c (fun s => by convert hfib s) f
  have hp := mp_prodMap hd (mp_equiv (Equiv.refl (Padding K F)))
  have hc := mp_comp (mp_comp (mp_equiv (spareEquiv (Input := Input) (F := F))) hp)
    (mp_equiv (completionEquiv (F := F)))
  intro f
  exact hc f

theorem quotient_success (decode : Input → Option (Tape K F)) (i : Input)
    (s : SourceTape K F) (hs : quotientDecode decode i = some s) :
    decode i = some ((decode i).getD (0, 0)) ∧
      project ((decode i).getD (0, 0)) = s := by
  cases hi : decode i with
  | none =>
    simp only [quotientDecode, hi, Option.map_none] at hs
    contradiction
  | some t =>
    simp only [Option.getD_some]
    exact ⟨trivial, Option.some.inj (by simpa only [quotientDecode, hi, Option.map_some] using hs)⟩

/-- Splitting a successful quotient fibre by its unique full-tape padding. -/
def projectedFibreEquiv (decode : Input → Option (Tape K F)) (s : SourceTape K F) :
    {i : Input // quotientDecode decode i = some s} ≃
      (p : Padding K F) × {i : Input // decode i = some (complete s p)} where
  toFun i := ⟨padding ((decode i.1).getD (0, 0)), i.1, by
    have ht := quotient_success decode i.1 s i.2
    exact ht.1.trans (congrArg some ((congrArg (fun q => complete q (padding ((decode i.1).getD (0, 0)))) ht.2).symm.trans (complete_project _)).symm)⟩
  invFun i := ⟨i.2.1, by simp [quotientDecode, i.2.2, project_complete]⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by
    rcases i with ⟨p, i, hi⟩
    apply Sigma.ext (by simp only [hi, Option.getD_some, padding_complete])
    apply (Subtype.heq_iff_coe_eq (fun j => by
      simp only [hi, Option.getD_some, padding_complete])).mpr
    rfl


theorem full_fibres_imply_quotient (decode : Input → Option (Tape K F)) (c : ℕ)
    (hfib : ∀ t, (Finset.univ.filter (fun i => decode i = some t)).card = c)
    (s : SourceTape K F) :
    (Finset.univ.filter (fun i => quotientDecode decode i = some s)).card =
      Fintype.card (Padding K F) * c := by
  have hc : ∀ p : Padding K F, Fintype.card {i : Input // decode i = some (complete s p)} = c := by
    intro p
    simpa only [Fintype.card_subtype] using hfib (complete s p)
  rw [← Fintype.card_subtype, Fintype.card_congr (projectedFibreEquiv decode s), Fintype.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]

#print axioms mp_completeOrSpare
#print axioms quotient_success
#print axioms projectedFibreEquiv
#print axioms full_fibres_imply_quotient
end R1Z.ProverCommitTapeCompletion
