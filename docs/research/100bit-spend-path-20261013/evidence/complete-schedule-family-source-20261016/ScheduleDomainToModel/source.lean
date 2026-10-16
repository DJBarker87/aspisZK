import ScheduleDomainArithmetic
import InitialSelectorPrefix

/-! Interpret the checked source domain/length chains with the retained
schedule coefficients, using structural base-field embedding identities. -/
set_option autoImplicit false
namespace AspisR1.ScheduleDomainToModel
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskScalarExact
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := CurrentCanonicalQM
abbrev Registers := AspisR1.InitialSelectorPrefix.Registers

def domainModel {K : Type} [Field K] (p : Registers K) : K :=
  (p.high0 * 1095958529 + ((p.high1 + p.high30) + p.transfer) * 1095958531) + p.high25 * 1095958530

def lengthModel {K : Type} [Field K] (p : Registers K) : K :=
  (p.high0 * 8 + ((p.high1 + p.high30) + p.transfer) * 18) + p.high25 * 16

theorem source_constant_embeddings :
    scalarEmbedding AspisR1.ScheduleDomainArithmetic.owner = (1095958529 : ExactQM) ∧
    scalarEmbedding AspisR1.ScheduleDomainArithmetic.note = (1095958531 : ExactQM) ∧
    scalarEmbedding AspisR1.ScheduleDomainArithmetic.nullifier = (1095958530 : ExactQM) ∧
    scalarEmbedding 8#u32 = (8 : ExactQM) ∧
    scalarEmbedding 18#u32 = (18 : ExactQM) ∧
    scalarEmbedding 16#u32 = (16 : ExactQM) := by
  have ho : AspisR1.ScheduleDomainArithmetic.owner.val = 1095958529 := by
    unfold AspisR1.ScheduleDomainArithmetic.owner AspisR1ScheduleDomainCandidate.spend.DOMAIN_OWNER_KEY
    scalar_tac
  have hn : AspisR1.ScheduleDomainArithmetic.note.val = 1095958531 := by
    unfold AspisR1.ScheduleDomainArithmetic.note AspisR1ScheduleDomainCandidate.spend.DOMAIN_NOTE
    scalar_tac
  have hnull : AspisR1.ScheduleDomainArithmetic.nullifier.val = 1095958530 := by
    unfold AspisR1.ScheduleDomainArithmetic.nullifier AspisR1ScheduleDomainCandidate.spend.DOMAIN_NULLIFIER
    scalar_tac
  have h8 : (8#u32).val = 8 := by scalar_tac
  have h18 : (18#u32).val = 18 := by scalar_tac
  have h16 : (16#u32).val = 16 := by scalar_tac
  simp only [AspisR1.ScheduleDomainArithmetic.scalarEmbedding_nat, ho, hn, hnull, h8, h18, h16, Nat.cast_ofNat, and_true]

theorem source_success (p : Registers QM)
    (hc : AspisR1.InitialSelectorPrefix.canonicalRegisters p) :
    ∃ domain length,
      AspisR1.ScheduleDomainArithmetic.run p.high0 p.high1 p.high25 p.high30 p.transfer = .ok (domain, length) ∧
      Canonical domain ∧ Canonical length ∧
      decode domain = domainModel (AspisR1.InitialSelectorPrefix.decodeRegisters p) ∧
      decode length = lengthModel (AspisR1.InitialSelectorPrefix.decodeRegisters p) := by
  rcases hc with ⟨_hc0, hc1, _hc25, hc30, _hcnodes, hct, _hcfixed, _hcEight, _hcTwo, _hclow, _hcfull, _hcrate⟩
  obtain ⟨domain, length, hrun, hcd, hcl, hvd, hvl⟩ :=
    AspisR1.ScheduleDomainArithmetic.source_success p.high0 p.high1 p.high25 p.high30 p.transfer hc1 hc30 hct
  rcases source_constant_embeddings with ⟨ho, hn, hnull, h8, h18, h16⟩
  refine ⟨domain, length, hrun, hcd, hcl, ?_, ?_⟩
  · simpa only [domainModel, AspisR1.InitialSelectorPrefix.decodeRegisters, ho, hn, hnull] using hvd
  · simpa only [lengthModel, AspisR1.InitialSelectorPrefix.decodeRegisters, h8, h18, h16] using hvl

#print axioms source_constant_embeddings
#print axioms source_success
end
end AspisR1.ScheduleDomainToModel
