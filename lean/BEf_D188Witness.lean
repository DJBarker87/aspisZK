import BEf_ExtractionGap
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_D188Witness
open Aeneas Aeneas.Std Result

def install (base : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : AdapterRw.Ops :=
  {base with op43 := S2W_DigestExtraction.digest hashv}

/-- An inhabited instance of the EXACT D188 record, using its actual owned
source functions. This is a model witness, not native/ELF association. -/
theorem instance_exists (base : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ first second, S2W_DigestExtraction.AeneasExtraction (install base hashv) first second hashv := by
  refine ⟨AdapterRw.r1_pool_adapter.owned.stage1_owned (install base hashv),
    AdapterRw.r1_pool_adapter.owned.stage2_owned (install base hashv),?_,?_,?_⟩
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _; rfl

/-- The missing carrier determination is compatible with a satisfiable D188
record; it is not obtained by adding inconsistent extraction hypotheses. -/
theorem carrier_independent (base : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (self : AdapterRw.SolanaDigest) (parts : S2Z.Oracle.Parts) :
    ∃ first second,
      S2W_DigestExtraction.AeneasExtraction (install base hashv) first second hashv ∧
      (BEf_ExtractionGap.retain ((install base hashv).op43 self) parts false).1 =
        (BEf_ExtractionGap.change ((install base hashv).op43 self) parts false).1 ∧
      (BEf_ExtractionGap.retain ((install base hashv).op43 self) parts false).2 ≠
        (BEf_ExtractionGap.change ((install base hashv).op43 self) parts false).2 := by
  obtain ⟨first,second,extraction⟩ := instance_exists base hashv
  exact ⟨first,second,extraction,rfl,BEf_ExtractionGap.different _ _⟩

#print axioms instance_exists
#print axioms carrier_independent
end AspisR1.BEf_D188Witness
end
