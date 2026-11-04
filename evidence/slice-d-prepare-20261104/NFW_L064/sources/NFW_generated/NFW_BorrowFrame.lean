import KMX_CopyMeaning
set_option autoImplicit false
namespace NFW_BorrowFrame
/-- Descriptor/byte framing. This is a memory-value law, not a replacement
protocol or hash. Native allocation validity and the representation map remain
inside the existing std/allocator/ABI and P6/D188 realization rows. -/
def observe {A : Type} (memory : Nat→A) (base offset : Nat) : A := memory (base+offset)
theorem same_view {A : Type} (memory : Nat→A) (base seen size seenSize offset : Nat)
 (address : seen=base) (length : seenSize=size) (inside : offset<size) :
 offset<seenSize ∧ observe memory seen offset=observe memory base offset := by
 subst seen
 subst seenSize
 exact ⟨inside,rfl⟩
/-- A write to an unrelated local log cannot change any byte in the immutable
input view; non-overlap is an explicit native caller obligation. -/
theorem log_frame {A : Type} (memory : Nat→A) (logAddress base size offset : Nat) (v : A)
 (inside : offset<size) (outside : logAddress<base ∨ base+size≤logAddress) :
 observe (KMX_CopyMeaning.write memory logAddress v) base offset=observe memory base offset := by
 unfold observe KMX_CopyMeaning.write
 apply if_neg
 omega
/-- The same frame for a finite disjoint output/log window, using the exact
KMX value law rather than a custom copy replacement. -/
theorem copy_frame {A : Type} (src memory : Nat→A) (start count base size offset : Nat)
 (inside : offset<size) (disjoint : start+count≤base ∨ base+size≤start) :
 observe (KMX_CopyMeaning.loop src memory start count) base offset=observe memory base offset := by
 unfold observe
 apply KMX_CopyMeaning.copy_frame
 omega
/-- Sparse one-window observation has the chosen value, with every other
memory cell left framed. This alone is not a whole native function theorem. -/
theorem sparse_cell {A : Type} (memory : Nat→A) (base offset : Nat) (v : A) :
 observe (KMX_CopyMeaning.write memory (base+offset) v) base offset=v := by
 simp [observe,KMX_CopyMeaning.write]
#print axioms same_view
#print axioms log_frame
#print axioms copy_frame
#print axioms sparse_cell
end NFW_BorrowFrame
