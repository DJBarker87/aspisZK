import JHb_DataEntry
set_option autoImplicit false
namespace AspisR1.JHg_AuditEntry
open Aeneas Aeneas.Std Result
/-- Frozen layout Entry[0:4); byte fact, not decoder/native refinement. -/
theorem magic : (JHb_DataEntry.bytes.drop 0).take 4 = [65#u8,83#u8,69#u8,50#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms magic
/-- Frozen layout Entry[4:5); byte fact, not decoder/native refinement. -/
theorem version : (JHb_DataEntry.bytes.drop 4).take 1 = List.replicate 1 3#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms version
/-- Frozen layout Entry[5:6); byte fact, not decoder/native refinement. -/
theorem status : (JHb_DataEntry.bytes.drop 5).take 1 = List.replicate 1 1#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms status
/-- Frozen layout Entry[6:7); byte fact, not decoder/native refinement. -/
theorem statement_version : (JHb_DataEntry.bytes.drop 6).take 1 = List.replicate 1 1#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms statement_version
/-- Frozen layout Entry[7:8); byte fact, not decoder/native refinement. -/
theorem mode : (JHb_DataEntry.bytes.drop 7).take 1 = List.replicate 1 1#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms mode
/-- Frozen layout Entry[8:40); byte fact, not decoder/native refinement. -/
theorem pool : (JHb_DataEntry.bytes.drop 8).take 32 = [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms pool
/-- Frozen layout Entry[40:72); byte fact, not decoder/native refinement. -/
theorem verifier : (JHb_DataEntry.bytes.drop 40).take 32 = [95#u8,12#u8,126#u8,84#u8,84#u8,184#u8,191#u8,44#u8,127#u8,237#u8,85#u8,250#u8,26#u8,65#u8,11#u8,162#u8,234#u8,180#u8,193#u8,149#u8,162#u8,190#u8,100#u8,247#u8,226#u8,253#u8,59#u8,0#u8,225#u8,151#u8,154#u8,141#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms verifier
/-- Frozen layout Entry[72:104); byte fact, not decoder/native refinement. -/
theorem profile : (JHb_DataEntry.bytes.drop 72).take 32 = [87#u8,148#u8,115#u8,19#u8,210#u8,50#u8,100#u8,26#u8,216#u8,21#u8,125#u8,102#u8,191#u8,175#u8,250#u8,177#u8,30#u8,76#u8,58#u8,153#u8,51#u8,29#u8,24#u8,244#u8,75#u8,250#u8,202#u8,182#u8,137#u8,151#u8,55#u8,211#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms profile
/-- Frozen layout Entry[104:136); byte fact, not decoder/native refinement. -/
theorem release : (JHb_DataEntry.bytes.drop 104).take 32 = [226#u8,148#u8,175#u8,188#u8,20#u8,239#u8,106#u8,254#u8,118#u8,184#u8,71#u8,222#u8,244#u8,68#u8,82#u8,248#u8,76#u8,195#u8,114#u8,128#u8,100#u8,101#u8,118#u8,7#u8,181#u8,68#u8,165#u8,57#u8,202#u8,155#u8,50#u8,58#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms release
/-- Frozen layout Entry[136:168); byte fact, not decoder/native refinement. -/
theorem loader : (JHb_DataEntry.bytes.drop 136).take 32 = [2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8,226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms loader
/-- Frozen layout Entry[168:200); byte fact, not decoder/native refinement. -/
theorem programdata : (JHb_DataEntry.bytes.drop 168).take 32 = [9#u8,32#u8,132#u8,147#u8,91#u8,179#u8,5#u8,145#u8,236#u8,128#u8,247#u8,235#u8,169#u8,248#u8,96#u8,190#u8,113#u8,27#u8,13#u8,169#u8,128#u8,213#u8,131#u8,59#u8,122#u8,113#u8,158#u8,205#u8,89#u8,140#u8,195#u8,110#u8] := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms programdata
/-- Frozen layout Entry[200:232); byte fact, not decoder/native refinement. -/
theorem executable_hash : (JHb_DataEntry.bytes.drop 200).take 32 = List.replicate 32 90#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms executable_hash
/-- Frozen layout Entry[232:264); byte fact, not decoder/native refinement. -/
theorem upgrade_authority : (JHb_DataEntry.bytes.drop 232).take 32 = List.replicate 32 0#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms upgrade_authority
/-- Frozen layout Entry[264:272); byte fact, not decoder/native refinement. -/
theorem activation : (JHb_DataEntry.bytes.drop 264).take 8 = List.replicate 8 0#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms activation
/-- Frozen layout Entry[272:280); byte fact, not decoder/native refinement. -/
theorem retirement : (JHb_DataEntry.bytes.drop 272).take 8 = List.replicate 8 255#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms retirement
/-- Frozen layout Entry[280:312); byte fact, not decoder/native refinement. -/
theorem policy : (JHb_DataEntry.bytes.drop 280).take 32 = List.replicate 32 7#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms policy
/-- Frozen layout Entry[312:313); byte fact, not decoder/native refinement. -/
theorem bump : (JHb_DataEntry.bytes.drop 312).take 1 = List.replicate 1 254#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms bump
/-- Frozen layout Entry[313:314); byte fact, not decoder/native refinement. -/
theorem programdata_bump : (JHb_DataEntry.bytes.drop 313).take 1 = List.replicate 1 254#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms programdata_bump
/-- Frozen layout Entry[314:320); byte fact, not decoder/native refinement. -/
theorem reserved : (JHb_DataEntry.bytes.drop 314).take 6 = List.replicate 6 0#u8 := by
  simp only [JHb_DataEntry.bytes,JHb_DataEntry.c00_length,JHb_DataEntry.c01_length,JHb_DataEntry.c02_length,JHb_DataEntry.c03_length,JHb_DataEntry.c04_length,JHb_DataEntry.c05_length,JHb_DataEntry.c06_length,JHb_DataEntry.c07_length,JHb_DataEntry.c08_length,JHb_DataEntry.c09_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms reserved
end AspisR1.JHg_AuditEntry
