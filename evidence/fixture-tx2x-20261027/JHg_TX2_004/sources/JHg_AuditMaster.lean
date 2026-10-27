import JHg_DataMaster
set_option autoImplicit false
namespace AspisR1.JHg_AuditMaster
open Aeneas Aeneas.Std Result
/-- Frozen layout Master[0:4); byte fact, not decoder/native refinement. -/
theorem magic : (JHg_DataMaster.bytes.drop 0).take 4 = [65#u8,83#u8,77#u8,56#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms magic
/-- Frozen layout Master[4:5); byte fact, not decoder/native refinement. -/
theorem version : (JHg_DataMaster.bytes.drop 4).take 1 = List.replicate 1 2#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms version
/-- Frozen layout Master[5:6); byte fact, not decoder/native refinement. -/
theorem lanes : (JHg_DataMaster.bytes.drop 5).take 1 = List.replicate 1 8#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lanes
/-- Frozen layout Master[6:7); byte fact, not decoder/native refinement. -/
theorem encoding : (JHg_DataMaster.bytes.drop 6).take 1 = List.replicate 1 1#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms encoding
/-- Frozen layout Master[7:8); byte fact, not decoder/native refinement. -/
theorem bump : (JHg_DataMaster.bytes.drop 7).take 1 = List.replicate 1 254#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms bump
/-- Frozen layout Master[8:40); byte fact, not decoder/native refinement. -/
theorem format : (JHg_DataMaster.bytes.drop 8).take 32 = [65#u8,83#u8,80#u8,73#u8,83#u8,70#u8,79#u8,82#u8,69#u8,83#u8,84#u8,56#u8,2#u8,2#u8,2#u8,8#u8,1#u8,20#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms format
/-- Frozen layout Master[40:48); byte fact, not decoder/native refinement. -/
theorem next_checkpoint : (JHg_DataMaster.bytes.drop 40).take 8 = [43#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms next_checkpoint
/-- Frozen layout Master[48:49); byte fact, not decoder/native refinement. -/
theorem lane_mask : (JHg_DataMaster.bytes.drop 48).take 1 = List.replicate 1 255#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_mask
/-- Frozen layout Master[49:50); byte fact, not decoder/native refinement. -/
theorem has_checkpoint : (JHg_DataMaster.bytes.drop 49).take 1 = List.replicate 1 1#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms has_checkpoint
/-- Frozen layout Master[50:64); byte fact, not decoder/native refinement. -/
theorem reserved0 : (JHg_DataMaster.bytes.drop 50).take 14 = List.replicate 14 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms reserved0
/-- Frozen layout Master[64:68); byte fact, not decoder/native refinement. -/
theorem identity_magic : (JHg_DataMaster.bytes.drop 64).take 4 = [65#u8,83#u8,80#u8,73#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms identity_magic
/-- Frozen layout Master[68:69); byte fact, not decoder/native refinement. -/
theorem identity_version : (JHg_DataMaster.bytes.drop 68).take 1 = List.replicate 1 1#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms identity_version
/-- Frozen layout Master[69:72); byte fact, not decoder/native refinement. -/
theorem identity_reserved : (JHg_DataMaster.bytes.drop 69).take 3 = List.replicate 3 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms identity_reserved
/-- Frozen layout Master[72:104); byte fact, not decoder/native refinement. -/
theorem pool : (JHg_DataMaster.bytes.drop 72).take 32 = [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms pool
/-- Frozen layout Master[104:136); byte fact, not decoder/native refinement. -/
theorem mint : (JHg_DataMaster.bytes.drop 104).take 32 = List.replicate 32 66#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms mint
/-- Frozen layout Master[136:168); byte fact, not decoder/native refinement. -/
theorem token : (JHg_DataMaster.bytes.drop 136).take 32 = [6#u8,221#u8,246#u8,225#u8,215#u8,101#u8,161#u8,147#u8,217#u8,203#u8,225#u8,70#u8,206#u8,235#u8,121#u8,172#u8,28#u8,180#u8,133#u8,237#u8,95#u8,91#u8,55#u8,145#u8,58#u8,140#u8,245#u8,133#u8,126#u8,255#u8,0#u8,169#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms token
/-- Frozen layout Master[168:172); byte fact, not decoder/native refinement. -/
theorem asset : (JHg_DataMaster.bytes.drop 168).take 4 = [77#u8,0#u8,0#u8,0#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms asset
/-- Frozen layout Master[172:176); byte fact, not decoder/native refinement. -/
theorem identity_reserved1 : (JHg_DataMaster.bytes.drop 172).take 4 = List.replicate 4 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms identity_reserved1
/-- Frozen layout Master[176:208); byte fact, not decoder/native refinement. -/
theorem domain : (JHg_DataMaster.bytes.drop 176).take 32 = List.replicate 32 5#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms domain
/-- Frozen layout Master[208:212); byte fact, not decoder/native refinement. -/
theorem policy_magic : (JHg_DataMaster.bytes.drop 208).take 4 = [65#u8,83#u8,80#u8,80#u8] := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy_magic
/-- Frozen layout Master[212:213); byte fact, not decoder/native refinement. -/
theorem policy_version : (JHg_DataMaster.bytes.drop 212).take 1 = List.replicate 1 1#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy_version
/-- Frozen layout Master[213:214); byte fact, not decoder/native refinement. -/
theorem policy_flags : (JHg_DataMaster.bytes.drop 213).take 1 = List.replicate 1 3#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy_flags
/-- Frozen layout Master[214:216); byte fact, not decoder/native refinement. -/
theorem policy_reserved : (JHg_DataMaster.bytes.drop 214).take 2 = List.replicate 2 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy_reserved
/-- Frozen layout Master[216:248); byte fact, not decoder/native refinement. -/
theorem registry_program : (JHg_DataMaster.bytes.drop 216).take 32 = List.replicate 32 68#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms registry_program
/-- Frozen layout Master[248:280); byte fact, not decoder/native refinement. -/
theorem registry_authority : (JHg_DataMaster.bytes.drop 248).take 32 = List.replicate 32 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms registry_authority
/-- Frozen layout Master[280:312); byte fact, not decoder/native refinement. -/
theorem policy_binding : (JHg_DataMaster.bytes.drop 280).take 32 = List.replicate 32 7#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy_binding
/-- Frozen layout Master[312:320); byte fact, not decoder/native refinement. -/
theorem reserved1 : (JHg_DataMaster.bytes.drop 312).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms reserved1
/-- Frozen layout Master[320:328); byte fact, not decoder/native refinement. -/
theorem last_sequence_0 : (JHg_DataMaster.bytes.drop 320).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_0
/-- Frozen layout Master[328:336); byte fact, not decoder/native refinement. -/
theorem last_sequence_1 : (JHg_DataMaster.bytes.drop 328).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_1
/-- Frozen layout Master[336:344); byte fact, not decoder/native refinement. -/
theorem last_sequence_2 : (JHg_DataMaster.bytes.drop 336).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_2
/-- Frozen layout Master[344:352); byte fact, not decoder/native refinement. -/
theorem last_sequence_3 : (JHg_DataMaster.bytes.drop 344).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_3
/-- Frozen layout Master[352:360); byte fact, not decoder/native refinement. -/
theorem last_sequence_4 : (JHg_DataMaster.bytes.drop 352).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_4
/-- Frozen layout Master[360:368); byte fact, not decoder/native refinement. -/
theorem last_sequence_5 : (JHg_DataMaster.bytes.drop 360).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_5
/-- Frozen layout Master[368:376); byte fact, not decoder/native refinement. -/
theorem last_sequence_6 : (JHg_DataMaster.bytes.drop 368).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_6
/-- Frozen layout Master[376:384); byte fact, not decoder/native refinement. -/
theorem last_sequence_7 : (JHg_DataMaster.bytes.drop 376).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataMaster.bytes,JHg_DataMaster.c00_length,JHg_DataMaster.c01_length,JHg_DataMaster.c02_length,JHg_DataMaster.c03_length,JHg_DataMaster.c04_length,JHg_DataMaster.c05_length,JHg_DataMaster.c06_length,JHg_DataMaster.c07_length,JHg_DataMaster.c08_length,JHg_DataMaster.c09_length,JHg_DataMaster.c10_length,JHg_DataMaster.c11_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms last_sequence_7
end AspisR1.JHg_AuditMaster
