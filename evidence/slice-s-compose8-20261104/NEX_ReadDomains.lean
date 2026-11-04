import NEX_DecoderDomains
set_option autoImplicit false
namespace NEX_ReadDomains
open Aeneas Aeneas.Std
/-- The real unrolled call counter enumerates exactly these digest windows. -/
theorem after_window (bytes : Array U8 688#usize) (n : Nat) (hn : n<21) :
    ((bytes.val.drop (16+32*n)).take 32).length=32 ∧
    16+32*n+32≤688 := by
  have length : bytes.val.length=688 := bytes.property
  simp only [List.length_take,List.length_drop,length]
  omega

theorem snapshot_window (bytes : Array U8 800#usize) (n : Nat) (hn : n<21) :
    ((bytes.val.drop (128+32*n)).take 32).length=32 ∧
    128+32*n+32≤800 := by
  have length : bytes.val.length=800 := bytes.property
  simp only [List.length_take,List.length_drop,length]
  omega

theorem after_scalar (bytes : Array U8 688#usize) :
    ((bytes.val.drop 8).take 8).length=8 := by
  have length : bytes.val.length=688 := bytes.property
  simp only [List.length_take,List.length_drop,length]
  decide

/-- One arbitrary digest byte belongs to this call, never its neighbour. -/
theorem disjoint (base a b i j : Nat) (hi : i<32) (hj : j<32)
    (same : base+32*a+i=base+32*b+j) : a=b ∧ i=j := by omega

#print axioms after_window
#print axioms snapshot_window
#print axioms after_scalar
#print axioms disjoint
end NEX_ReadDomains
