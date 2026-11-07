import PCI_SingleRef.Funs
import PCI_ArrayCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SingleExtracted

def answer (d : Array U32 8#usize) (valid : Bool) : PCI_SingleRef.Single :=
  if valid then {tag:=0#u8,first:=d,occupied:=0#u32,second:=Array.repeat 8#usize 0#u32,inverse:=0#u32}
  else {tag:=1#u8,first:=Array.repeat 8#usize 0#u32,occupied:=0#u32,second:=Array.repeat 8#usize 0#u32,inverse:=0#u32}

theorem extracted (d : Array U32 8#usize) :
    PCI_SingleRef.single_reference d=ok (answer d (PCI_ArrayCanonical.model d)) := by
  unfold PCI_SingleRef.single_reference answer PCI_ArrayCanonical.model
  simp only [PCF_ArrayIndex.result d 0#usize (by scalar_tac),PCF_ArrayIndex.result d 1#usize (by scalar_tac),PCF_ArrayIndex.result d 2#usize (by scalar_tac),PCF_ArrayIndex.result d 3#usize (by scalar_tac),PCF_ArrayIndex.result d 4#usize (by scalar_tac),PCF_ArrayIndex.result d 5#usize (by scalar_tac),PCF_ArrayIndex.result d 6#usize (by scalar_tac),PCF_ArrayIndex.result d 7#usize (by scalar_tac),bind_tc_ok]
  by_cases h0 : d.val[0]!.val<2147483647
  · simp only [h0,ite_true,decide_true]
    by_cases h1 : d.val[1]!.val<2147483647
    · simp only [h1,ite_true,decide_true]
      by_cases h2 : d.val[2]!.val<2147483647
      · simp only [h2,ite_true,decide_true]
        by_cases h3 : d.val[3]!.val<2147483647
        · simp only [h3,ite_true,decide_true]
          by_cases h4 : d.val[4]!.val<2147483647
          · simp only [h4,ite_true,decide_true]
            by_cases h5 : d.val[5]!.val<2147483647
            · simp only [h5,ite_true,decide_true]
              by_cases h6 : d.val[6]!.val<2147483647
              · simp only [h6,ite_true,decide_true]
                by_cases h7 : d.val[7]!.val<2147483647
                · simp only [h7,ite_true,decide_true]
                  simp only [decide_true,ite_true]
                · simp only [h7,ite_false,decide_false,Bool.false_eq_true]
              · simp only [h6,ite_false,decide_false,Bool.false_eq_true]
            · simp only [h5,ite_false,decide_false,Bool.false_eq_true]
          · simp only [h4,ite_false,decide_false,Bool.false_eq_true]
        · simp only [h3,ite_false,decide_false,Bool.false_eq_true]
      · simp only [h2,ite_false,decide_false,Bool.false_eq_true]
    · simp only [h1,ite_false,decide_false,Bool.false_eq_true]
  · simp only [h0,ite_false,decide_false,Bool.false_eq_true]

#print axioms extracted
end PCI_SingleExtracted
