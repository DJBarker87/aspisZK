import NBR_SemanticStep
import NCA_SerializerWindow
set_option autoImplicit false
namespace AspisR1.NCA_SemanticFrames
open Aeneas Aeneas.Std

/-- General full logical-carrier window law. Instantiations below retain the
same14759-byte allocation, including the y1 exterior. -/
theorem window (out : Array U8 14759#usize) {n : Usize} (bytes : Array U8 n)
    (start j : Nat) (room : start+n.val≤14759) (index : j<14759) :
    (out.setSlice! start bytes.val).val[j]! =
      if start≤j ∧ j<start+n.val then bytes.val[j-start]! else out.val[j]! := by
  by_cases inside : start≤j ∧ j<start+n.val
  · rw [if_pos inside]
    have mid := Array.setSlice!_getElem!_middle out bytes.val start j
      (by have size:=bytes.property;scalar_tac)
    simpa only [Array.getElem!_Nat_eq] using mid
  · rw [if_neg inside]
    by_cases early : j<start
    · simpa only [Array.getElem!_Nat_eq] using
        Array.setSlice!_getElem!_prefix out bytes.val start j early
    · have late : start+bytes.val.length≤j := by rw [bytes.property];omega
      simpa only [Array.getElem!_Nat_eq] using
        Array.setSlice!_getElem!_suffix out bytes.val start j late

/-- Native root-window value/frame specification on the actual allocation. -/
theorem root (out : Array U8 14759#usize) (bytes : Array U8 32#usize)
    (j : Nat) (index : j<14759) :
    (out.setSlice! 0 bytes.val).val[j]! = if j<32 then bytes.val[j]! else out.val[j]! := by
  simpa only [Nat.zero_add,Nat.zero_le,true_and,Nat.sub_zero,UScalar.ofNatCore_val_eq] using
    window out bytes 0 j (by decide) index

/-- Every row header is in the semantic slice; all y1 bytes are exterior. -/
theorem header_domain (row : Nat) (bound : row<27) :
    JFw_Geometry.destPos row+5≤13831 ∧
      (∀ j, 13831≤j → ¬ (JFw_Geometry.destPos row≤j ∧ j<JFw_Geometry.destPos row+5)) := by
  obtain ⟨_,_,_,next,_,endBound⟩ := JFw_Geometry.step row bound
  constructor
  · omega
  · intro j suffix inside
    omega

#print axioms window
#print axioms root
#print axioms header_domain
end AspisR1.NCA_SemanticFrames
