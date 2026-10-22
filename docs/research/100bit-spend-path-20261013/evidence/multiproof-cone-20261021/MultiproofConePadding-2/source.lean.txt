import MultiproofConeCanonical

set_option autoImplicit false
namespace AspisR1.MultiproofConePadding
open AspisV8R19.DuplexFrames

/-- Composition of the verified 8-byte zero-word cut. A partial suffix is
ignored just as chunks_exact ignores it; the slot-width theorem rules it out. -/
def scan : Nat → Bytes → Bool
  | 0,_ => true
  | words+1,bs => if bs.length<8 then true else
      (bs.take 8).all (fun b => b==0) && scan words (bs.drop 8)

theorem scan_all (words : Nat) (bs : Bytes) (length : bs.length=8*words) :
    scan words bs=bs.all (fun b => b==0) := by
  induction words generalizing bs with
  | zero => have empty : bs=[] := List.length_eq_zero_iff.mp (by omega);subst bs;rfl
  | succ words ih =>
    have enough : ¬bs.length<8 := by omega
    have tailLength : (bs.drop 8).length=8*words := by rw [List.length_drop,length];omega
    rw [scan,if_neg enough,ih _ tailLength]
    have split : bs.all (fun b => b==0) =
        ((bs.take 8).all (fun b => b==0) && (bs.drop 8).all (fun b => b==0)) := by
      conv_lhs => rw [←List.take_append_drop 8 bs]
      exact List.all_append
    exact split.symm

/-- Whole-word zero padding is exactly the frozen byte equality, with no
ignored short tail under the independently known slot width. -/
theorem padding (cap count : Nat) (bs : Bytes) (width : bs.length=32*cap)
    (fit : count≤cap) :
    scan (4*(cap-count)) (bs.drop (32*count))=true ↔
      bs.drop (32*count)=List.replicate (32*(cap-count)) 0 := by
  have len : (bs.drop (32*count)).length=8*(4*(cap-count)) := by
    rw [List.length_drop,width];omega
  rw [scan_all _ _ len]
  simp only [List.all_eq_true,beq_iff_eq,List.eq_replicate_iff]
  constructor
  · intro all
    exact ⟨by rw [len];omega,all⟩
  · exact fun h => h.2

#print axioms scan_all
#print axioms padding
end AspisR1.MultiproofConePadding
