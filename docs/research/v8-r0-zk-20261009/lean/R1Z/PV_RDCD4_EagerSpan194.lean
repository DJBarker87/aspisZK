import R1Z.PV_RDCD4_BlockLayout194
import R1Z.PV_RDCD4_MemorySplit194
set_option autoImplicit false
namespace R1Z.PV_RDCD4_EagerSpan194
open Aeneas Aeneas.Std Result PV_RDCD4_Memory194

/-- Byte-footprint view of the two native borrowed slices. The typed
GenericArray carrier conversion is a separate, still required bridge. -/
def source (s : Span U8) : Span U8 × Span U8 :=
  let nb := s.len/64
  let used := nb*64
  (sliceRawFromRawParts s.pointer used,
   sliceRawFromRawParts (advance s.pointer used) (s.len-used))

theorem split_binding (s : Span U8) :
    source s=PV_RDCD4_MemorySplit194.split s ((s.len/64)*64) := rfl

theorem values (s : Span U8) :
    PV_RDCD4_Memory194.values (source s).1=
      (PV_RDCD4_Memory194.values s).take ((s.len/64)*64) ∧
    PV_RDCD4_Memory194.values (source s).2=
      (PV_RDCD4_Memory194.values s).drop ((s.len/64)*64) := by
  rw [split_binding]
  exact ⟨PV_RDCD4_MemorySplit194.left_values s _ (Nat.div_mul_le_self _ _),
    PV_RDCD4_MemorySplit194.right_values s _⟩

theorem partition (s : Span U8) :
    PV_RDCD4_Memory194.values (source s).1 ++
      PV_RDCD4_Memory194.values (source s).2=PV_RDCD4_Memory194.values s := by
  rw [split_binding]
  exact PV_RDCD4_MemorySplit194.partition s _ (Nat.div_mul_le_self _ _)

theorem valid_parts (s : Span U8) (h : valid s.pointer s.len) :
    valid (source s).1.pointer (source s).1.len ∧
      valid (source s).2.pointer (source s).2.len := by
  rw [split_binding]
  exact PV_RDCD4_MemorySplit194.valid_parts s _ h (Nat.div_mul_le_self _ _)

theorem aliases (s : Span U8) :
    (source s).1.pointer=s.pointer ∧
    (source s).2.pointer.origin=s.pointer.origin ∧
    (source s).2.pointer.data=s.pointer.data ∧
    (source s).2.pointer.offset=s.pointer.offset+(s.len/64)*64 := by
  rw [split_binding]
  exact PV_RDCD4_MemorySplit194.aliases s _
#print axioms split_binding
#print axioms values
#print axioms partition
#print axioms valid_parts
#print axioms aliases
end R1Z.PV_RDCD4_EagerSpan194
