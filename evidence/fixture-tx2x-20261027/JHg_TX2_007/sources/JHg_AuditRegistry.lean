import JHb_DataRegistry
set_option autoImplicit false
namespace AspisR1.JHg_AuditRegistry
open Aeneas Aeneas.Std Result
/-- Frozen layout Registry[0:4); byte fact, not decoder/native refinement. -/
theorem magic : (JHb_DataRegistry.bytes.drop 0).take 4 = [65#u8,83#u8,82#u8,50#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms magic
/-- Frozen layout Registry[4:5); byte fact, not decoder/native refinement. -/
theorem version : (JHb_DataRegistry.bytes.drop 4).take 1 = List.replicate 1 3#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms version
/-- Frozen layout Registry[5:6); byte fact, not decoder/native refinement. -/
theorem flags : (JHb_DataRegistry.bytes.drop 5).take 1 = List.replicate 1 2#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms flags
/-- Frozen layout Registry[6:7); byte fact, not decoder/native refinement. -/
theorem mode : (JHb_DataRegistry.bytes.drop 6).take 1 = List.replicate 1 1#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms mode
/-- Frozen layout Registry[7:8); byte fact, not decoder/native refinement. -/
theorem bump : (JHb_DataRegistry.bytes.drop 7).take 1 = List.replicate 1 255#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms bump
/-- Frozen layout Registry[8:40); byte fact, not decoder/native refinement. -/
theorem pool : (JHb_DataRegistry.bytes.drop 8).take 32 = [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms pool
/-- Frozen layout Registry[40:72); byte fact, not decoder/native refinement. -/
theorem authority : (JHb_DataRegistry.bytes.drop 40).take 32 = List.replicate 32 0#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms authority
/-- Frozen layout Registry[72:104); byte fact, not decoder/native refinement. -/
theorem policy : (JHb_DataRegistry.bytes.drop 72).take 32 = List.replicate 32 7#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy
/-- Frozen layout Registry[104:112); byte fact, not decoder/native refinement. -/
theorem generation : (JHb_DataRegistry.bytes.drop 104).take 8 = [1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms generation
/-- Frozen layout Registry[112:120); byte fact, not decoder/native refinement. -/
theorem delay : (JHb_DataRegistry.bytes.drop 112).take 8 = [1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms delay
/-- Frozen layout Registry[120:152); byte fact, not decoder/native refinement. -/
theorem program : (JHb_DataRegistry.bytes.drop 120).take 32 = List.replicate 32 68#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms program
/-- Frozen layout Registry[152:184); byte fact, not decoder/native refinement. -/
theorem loader : (JHb_DataRegistry.bytes.drop 152).take 32 = [2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8,226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms loader
/-- Frozen layout Registry[184:216); byte fact, not decoder/native refinement. -/
theorem programdata : (JHb_DataRegistry.bytes.drop 184).take 32 = [10#u8,229#u8,72#u8,238#u8,230#u8,11#u8,166#u8,244#u8,18#u8,189#u8,102#u8,59#u8,14#u8,251#u8,113#u8,3#u8,126#u8,115#u8,18#u8,70#u8,185#u8,8#u8,39#u8,166#u8,11#u8,127#u8,135#u8,77#u8,165#u8,209#u8,161#u8,69#u8] := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms programdata
/-- Frozen layout Registry[216:248); byte fact, not decoder/native refinement. -/
theorem executable_hash : (JHb_DataRegistry.bytes.drop 216).take 32 = List.replicate 32 165#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms executable_hash
/-- Frozen layout Registry[248:249); byte fact, not decoder/native refinement. -/
theorem programdata_bump : (JHb_DataRegistry.bytes.drop 248).take 1 = List.replicate 1 255#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms programdata_bump
/-- Frozen layout Registry[249:256); byte fact, not decoder/native refinement. -/
theorem reserved : (JHb_DataRegistry.bytes.drop 249).take 7 = List.replicate 7 0#u8 := by
  simp only [JHb_DataRegistry.bytes,JHb_DataRegistry.c00_length,JHb_DataRegistry.c01_length,JHb_DataRegistry.c02_length,JHb_DataRegistry.c03_length,JHb_DataRegistry.c04_length,JHb_DataRegistry.c05_length,JHb_DataRegistry.c06_length,JHb_DataRegistry.c07_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms reserved
end AspisR1.JHg_AuditRegistry
