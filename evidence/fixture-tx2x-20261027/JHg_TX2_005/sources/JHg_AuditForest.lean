import JHg_DataForest
set_option autoImplicit false
namespace AspisR1.JHg_AuditForest
open Aeneas Aeneas.Std Result
/-- Frozen layout Forest[0:4); byte fact, not decoder/native refinement. -/
theorem magic : (JHg_DataForest.bytes.drop 0).take 4 = [65#u8,83#u8,67#u8,56#u8] := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms magic
/-- Frozen layout Forest[4:5); byte fact, not decoder/native refinement. -/
theorem version : (JHg_DataForest.bytes.drop 4).take 1 = List.replicate 1 2#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms version
/-- Frozen layout Forest[5:6); byte fact, not decoder/native refinement. -/
theorem lanes : (JHg_DataForest.bytes.drop 5).take 1 = List.replicate 1 8#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lanes
/-- Frozen layout Forest[6:7); byte fact, not decoder/native refinement. -/
theorem encoding : (JHg_DataForest.bytes.drop 6).take 1 = List.replicate 1 1#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms encoding
/-- Frozen layout Forest[7:8); byte fact, not decoder/native refinement. -/
theorem bump : (JHg_DataForest.bytes.drop 7).take 1 = List.replicate 1 254#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms bump
/-- Frozen layout Forest[8:40); byte fact, not decoder/native refinement. -/
theorem master : (JHg_DataForest.bytes.drop 8).take 32 = [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8] := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms master
/-- Frozen layout Forest[40:72); byte fact, not decoder/native refinement. -/
theorem domain : (JHg_DataForest.bytes.drop 40).take 32 = List.replicate 32 5#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms domain
/-- Frozen layout Forest[72:80); byte fact, not decoder/native refinement. -/
theorem sequence : (JHg_DataForest.bytes.drop 72).take 8 = [42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms sequence
/-- Frozen layout Forest[80:112); byte fact, not decoder/native refinement. -/
theorem root : (JHg_DataForest.bytes.drop 80).take 32 = [85#u8,246#u8,62#u8,4#u8,159#u8,80#u8,117#u8,33#u8,221#u8,239#u8,128#u8,120#u8,216#u8,131#u8,141#u8,49#u8,99#u8,239#u8,102#u8,35#u8,253#u8,148#u8,147#u8,6#u8,128#u8,120#u8,67#u8,103#u8,86#u8,177#u8,157#u8,56#u8] := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms root
/-- Frozen layout Forest[112:120); byte fact, not decoder/native refinement. -/
theorem lane_sequence_0 : (JHg_DataForest.bytes.drop 112).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_0
/-- Frozen layout Forest[120:128); byte fact, not decoder/native refinement. -/
theorem lane_sequence_1 : (JHg_DataForest.bytes.drop 120).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_1
/-- Frozen layout Forest[128:136); byte fact, not decoder/native refinement. -/
theorem lane_sequence_2 : (JHg_DataForest.bytes.drop 128).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_2
/-- Frozen layout Forest[136:144); byte fact, not decoder/native refinement. -/
theorem lane_sequence_3 : (JHg_DataForest.bytes.drop 136).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_3
/-- Frozen layout Forest[144:152); byte fact, not decoder/native refinement. -/
theorem lane_sequence_4 : (JHg_DataForest.bytes.drop 144).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_4
/-- Frozen layout Forest[152:160); byte fact, not decoder/native refinement. -/
theorem lane_sequence_5 : (JHg_DataForest.bytes.drop 152).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_5
/-- Frozen layout Forest[160:168); byte fact, not decoder/native refinement. -/
theorem lane_sequence_6 : (JHg_DataForest.bytes.drop 160).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_6
/-- Frozen layout Forest[168:176); byte fact, not decoder/native refinement. -/
theorem lane_sequence_7 : (JHg_DataForest.bytes.drop 168).take 8 = List.replicate 8 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms lane_sequence_7
/-- Frozen layout Forest[176:192); byte fact, not decoder/native refinement. -/
theorem reserved : (JHg_DataForest.bytes.drop 176).take 16 = List.replicate 16 0#u8 := by
  simp only [JHg_DataForest.bytes,JHg_DataForest.c00_length,JHg_DataForest.c01_length,JHg_DataForest.c02_length,JHg_DataForest.c03_length,JHg_DataForest.c04_length,JHg_DataForest.c05_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms reserved
end AspisR1.JHg_AuditForest
