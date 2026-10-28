import NDO_JHs_PDA
import NDO_JHj_RegistrySeeds
set_option autoImplicit false
namespace AspisR1.JHs_Inputs
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open AspisV8R19.SqueezeOracleBridge
namespace Master
def raw : List Nat := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 109, 97, 115, 116, 101, 114, 45, 118, 49, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 254, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_Seeds.master JHb_Programs.pool).map Fin.val = raw := by
  simp only [JHs_PDA.preimage, JHj_Seeds.master, JHj_Seeds.key, Array.to_slice,
    Array.make, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [JHg_PDAFields.master_seed]
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_Seeds.master := by
  change (JHj_Seeds.master).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_Seeds.master, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1 | h2
    · subst seed
      rw [JHg_PDAFields.master_seed]
      decide
    · subst seed
      decide
    · subst seed
      decide
#print axioms valid
end Master
namespace Checkpoint
def raw : List Nat := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 99, 104, 101, 99, 107, 112, 111, 105, 110, 116, 45, 118, 49, 34, 8, 198, 55, 61, 211, 19, 178, 242, 118, 165, 45, 20, 254, 147, 25, 55, 157, 211, 124, 152, 170, 59, 88, 182, 77, 252, 152, 45, 26, 82, 63, 42, 0, 0, 0, 0, 0, 0, 0, 254, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_Seeds.checkpoint JHb_Programs.pool).map Fin.val = raw := by
  simp only [JHs_PDA.preimage, JHj_Seeds.checkpoint, JHj_Seeds.key, Array.to_slice,
    Array.make, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [JHg_PDAFields.forest_seed,JHg_PDAFields.master_key]
  have serial : (core.num.U64.to_le_bytes 42#u64).val =
      [42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
    simp [core.num.U64.to_le_bytes, BitVec.toLEBytes]
    constructor <;> rfl
  simp only [JHg_AccountValues.checkpoint, JHg_Scalar09.native]
  rw [serial]
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_Seeds.checkpoint := by
  change (JHj_Seeds.checkpoint).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_Seeds.checkpoint, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1 | h2 | h3
    · subst seed
      rw [JHg_PDAFields.forest_seed]
      decide
    · subst seed
      exact Nat.le_of_eq JHj_Seeds.key.property
    · subst seed
      change (core.num.U64.to_le_bytes JHg_AccountValues.checkpoint.checkpoint_sequence).val.length ≤ 32
      rw [(core.num.U64.to_le_bytes JHg_AccountValues.checkpoint.checkpoint_sequence).property]
      decide
    · subst seed
      decide
#print axioms valid
end Checkpoint
namespace Lane
def raw : List Nat := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 108, 97, 110, 101, 45, 118, 49, 34, 8, 198, 55, 61, 211, 19, 178, 242, 118, 165, 45, 20, 254, 147, 25, 55, 157, 211, 124, 152, 170, 59, 88, 182, 77, 252, 152, 45, 26, 82, 63, 3, 255, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_Seeds.lane JHb_Programs.pool).map Fin.val = raw := by
  simp only [JHs_PDA.preimage, JHj_Seeds.lane, JHj_Seeds.key, Array.to_slice,
    Array.make, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [JHg_PDAFields.lane_seed,JHg_PDAFields.master_key]
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_Seeds.lane := by
  change (JHj_Seeds.lane).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_Seeds.lane, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1 | h2 | h3
    · subst seed
      rw [JHg_PDAFields.lane_seed]
      decide
    · subst seed
      exact Nat.le_of_eq JHj_Seeds.key.property
    · subst seed
      decide
    · subst seed
      decide
#print axioms valid
end Lane
namespace Registry
def raw : List Nat := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 114, 101, 103, 105, 115, 116, 114, 121, 45, 118, 50, 34, 8, 198, 55, 61, 211, 19, 178, 242, 118, 165, 45, 20, 254, 147, 25, 55, 157, 211, 124, 152, 170, 59, 88, 182, 77, 252, 152, 45, 26, 82, 63, 255, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_RegistrySeeds.registry JHb_Programs.registry).map Fin.val = raw := by
  simp only [JHs_PDA.preimage, JHj_RegistrySeeds.registry, JHj_Seeds.key, Array.to_slice,
    Array.make, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [JHg_PDAFields.registry_seed,JHg_PDAFields.master_key]
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_RegistrySeeds.registry := by
  change (JHj_RegistrySeeds.registry).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_RegistrySeeds.registry, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1 | h2
    · subst seed
      rw [JHg_PDAFields.registry_seed]
      decide
    · subst seed
      exact Nat.le_of_eq JHj_Seeds.key.property
    · subst seed
      decide
#print axioms valid
end Registry
namespace RegistryProgramdata
def raw : List Nat := [68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 255, 2, 168, 246, 145, 78, 136, 161, 176, 226, 16, 21, 62, 247, 99, 174, 43, 0, 194, 185, 61, 22, 193, 36, 210, 192, 83, 122, 16, 4, 128, 0, 0, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader).map Fin.val = raw := by
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_RegistrySeeds.registryProgramdata := by
  change (JHj_RegistrySeeds.registryProgramdata).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_RegistrySeeds.registryProgramdata, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1
    · subst seed
      decide
    · subst seed
      decide
#print axioms valid
end RegistryProgramdata
namespace Entry
def raw : List Nat := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 101, 110, 116, 114, 121, 45, 118, 50, 34, 8, 198, 55, 61, 211, 19, 178, 242, 118, 165, 45, 20, 254, 147, 25, 55, 157, 211, 124, 152, 170, 59, 88, 182, 77, 252, 152, 45, 26, 82, 63, 87, 148, 115, 19, 210, 50, 100, 26, 216, 21, 125, 102, 191, 175, 250, 177, 30, 76, 58, 153, 51, 29, 24, 244, 75, 250, 202, 182, 137, 151, 55, 211, 226, 148, 175, 188, 20, 239, 106, 254, 118, 184, 71, 222, 244, 68, 82, 248, 76, 195, 114, 128, 100, 101, 118, 7, 181, 68, 165, 57, 202, 155, 50, 58, 254, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_RegistrySeeds.entry JHb_Programs.registry).map Fin.val = raw := by
  simp only [JHs_PDA.preimage, JHj_RegistrySeeds.entry, JHj_Seeds.key, Array.to_slice,
    Array.make, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [JHg_PDAFields.entry_seed,JHg_PDAFields.master_key]
  unfold r1_pool_adapter.PROFILE_BINDING r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_RegistrySeeds.entry := by
  change (JHj_RegistrySeeds.entry).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_RegistrySeeds.entry, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1 | h2 | h3 | h4
    · subst seed
      rw [JHg_PDAFields.entry_seed]
      decide
    · subst seed
      exact Nat.le_of_eq JHj_Seeds.key.property
    · subst seed
      exact Nat.le_of_eq r1_pool_adapter.PROFILE_BINDING.property
    · subst seed
      exact Nat.le_of_eq r1_pool_adapter.RELEASE_BINDING.property
    · subst seed
      decide
#print axioms valid
end Entry
namespace VerifierProgramdata
def raw : List Nat := [95, 12, 126, 84, 84, 184, 191, 44, 127, 237, 85, 250, 26, 65, 11, 162, 234, 180, 193, 149, 162, 190, 100, 247, 226, 253, 59, 0, 225, 151, 154, 141, 254, 2, 168, 246, 145, 78, 136, 161, 176, 226, 16, 21, 62, 247, 99, 174, 43, 0, 194, 185, 61, 22, 193, 36, 210, 192, 83, 122, 16, 4, 128, 0, 0, 80, 114, 111, 103, 114, 97, 109, 68, 101, 114, 105, 118, 101, 100, 65, 100, 100, 114, 101, 115, 115]
theorem native : (JHs_PDA.preimage JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader).map Fin.val = raw := by
  rfl
#print axioms native
theorem valid : JHs_PDA.ValidSeeds JHj_RegistrySeeds.verifierProgramdata := by
  change (JHj_RegistrySeeds.verifierProgramdata).val.length ≤ 16 ∧ _
  constructor
  · decide
  · intro seed mem
    simp only [JHj_RegistrySeeds.verifierProgramdata, Array.to_slice, Array.make, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with h0 | h1
    · subst seed
      decide
    · subst seed
      decide
#print axioms valid
end VerifierProgramdata
end AspisR1.JHs_Inputs
