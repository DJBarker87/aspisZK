import R1Z.PV_CB3_StagedPipelineBits
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedValue
open Aeneas Aeneas.Std
open PV_CB3_StagedPacking

theorem bit_values {n : Usize} (a : Array U32 n) :
    (bits a).map BitVec.toNat = a.val.map UScalar.val := by
  simp only [bits,List.map_map,Function.comp_def,UScalar.bv_toNat]

theorem kernel_bits (rank : Array U32 8#usize) :
    bits (PV_CB3_StagedKernel.pipeline rank) = PV_CB3_MachineGamma.gamma (bits rank) := by
  rw [PV_CB3_StagedPipelineBits.kernel_pipeline]
  exact PV_CB3_StagedPipelineBits.bits_pipeline rank

theorem kernel_canonical (rank : Array U32 8#usize) (d : U32)
    (hd : d ∈ (PV_CB3_StagedKernel.pipeline rank).val) :
    d.val < PV_CB3_SamplerWord.base := by
  have hm : d.bv ∈ bits (PV_CB3_StagedKernel.pipeline rank) := List.mem_map.mpr ⟨d,hd,rfl⟩
  rw [kernel_bits] at hm
  have hc := PV_CB3_MachineGamma.canonical (bits rank) (bits_length rank) d.bv hm
  simpa only [UScalar.bv_toNat] using hc

theorem kernel_value (rank : Array U32 8#usize) :
    PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
      ((PV_CB3_StagedKernel.pipeline rank).val.map UScalar.val) =
    PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.radix (rank.val.map UScalar.val) %
      (PV_CB3_SamplerWord.base ^ 8 - 1) + 1 := by
  have h := PV_CB3_MachineGamma.value_formula (bits rank) (bits_length rank)
  rw [← kernel_bits] at h
  simpa only [bit_values] using h
#print axioms bit_values
#print axioms kernel_bits
#print axioms kernel_canonical
#print axioms kernel_value
end R1Z.PV_CB3_StagedValue
