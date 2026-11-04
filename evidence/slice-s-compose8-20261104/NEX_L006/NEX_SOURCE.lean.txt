import NEX_CommonOracle
set_option autoImplicit false
namespace NEX_DecoderDomains
open Aeneas Aeneas.Std
/-- These are the exact frozen offsets. Native pointer/argument association is
separate; list geometry alone earns no native credit. -/
theorem common_windows (bytes : Array U8 1880#usize) :
    ((bytes.val.drop 112).take 32).length=32 ∧
    ((bytes.val.drop 144).take 1520).length=1520 ∧
    ((bytes.val.drop 1664).take 216).length=216 := by
  have length : bytes.val.length=1880 := bytes.property
  simp only [List.length_take,List.length_drop,length]
  decide

theorem late_windows (bytes : Array U8 1520#usize) :
    ((bytes.val.drop 32).take 800).length=800 ∧
    (bytes.val.drop 832).length=688 := by
  have length : bytes.val.length=1520 := bytes.property
  simp only [List.length_take,List.length_drop,length]
  decide

theorem common_reads (j : Nat) (byte : j<32) :
    7<1880 ∧ 8+j<40 ∧ 40+j<72 ∧ 72+j<104 ∧
    104+8=112 ∧ 112+j<144 ∧ 144+1520=1664 ∧ 1664+216=1880 := by omega

theorem header_and_children_disjoint :
    32≤832 ∧ 832+688=1520 ∧ 144+1520=1664 ∧ 1664≤1880 := by decide

#print axioms common_windows
#print axioms late_windows
#print axioms common_reads
#print axioms header_and_children_disjoint
end NEX_DecoderDomains
