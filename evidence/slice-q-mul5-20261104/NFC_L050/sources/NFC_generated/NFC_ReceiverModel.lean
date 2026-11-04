import NFC_ArrayFour
import NFC_PacketDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_ReceiverModel
open Aeneas Aeneas.Std Result NFC_TailTrace

def words (state : Acc) : Array U64 8#usize :=
  Array.make 8#usize [state.c0.sums.val[0]!,state.c0.sums.val[1]!,state.c0.sums.val[2]!,state.c0.sums.val[3]!,
    state.c1.sums.val[0]!,state.c1.sums.val[1]!,state.c1.sums.val[2]!,state.c1.sums.val[3]!]
def restore (words : Array U64 8#usize) (count : Usize) : Acc :=
  ⟨⟨Array.make 4#usize [words.val[0]!,words.val[1]!,words.val[2]!,words.val[3]!]⟩,
   ⟨Array.make 4#usize [words.val[4]!,words.val[5]!,words.val[6]!,words.val[7]!]⟩,count⟩
def overwrite (before : Acc) (reply : Array U64 8#usize) : Acc :=
  restore reply (Usize.wrapping_add before.count 1#usize)

theorem roundtrip (state : Acc) : restore (words state) state.count=state := by
  rcases state with ⟨⟨left⟩,⟨right⟩,count⟩
  obtain ⟨a,b,c,d,hl⟩:=NFC_ArrayFour.shape left
  obtain ⟨e,f,g,h,hr⟩:=NFC_ArrayFour.shape right
  subst left
  subst right
  rfl

/-- The native owned reply permits the exact actual callee output; no
arithmetic value is selected independently of that actual call. -/
theorem represents (before after : Acc) (small : before.count.val<3)
    (count : after.count.val=before.count.val+1) :
    overwrite before (words after)=after := by
  have equal : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change (before.count.val+1)%UScalar.size .Usize=after.count.val
    have limit:=(4096#usize).hSize
    change 4096<UScalar.size .Usize at limit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [overwrite,equal,roundtrip]
#print axioms roundtrip
#print axioms represents
end AspisR1.NFC_ReceiverModel
end
