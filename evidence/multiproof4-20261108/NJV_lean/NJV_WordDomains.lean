import NJV_RowDomains

set_option autoImplicit false
noncomputable section
namespace NJV_WordDomains
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel

def Words (s : Scratch) : Prop := ∀ k, s.indices k<2^32

theorem initial (s : MultiproofConeRef.reference.Scratch) : Words (NJP_ScratchCarrier.raw s) :=
 NJP_ScratchCarrier.index_bound s

theorem index (s : Scratch) (words : Words s) (i : Nat) : NJP_RowModel.index s i<2^32 := by
 by_cases small : i<16
 · simpa only [NJP_RowModel.index,dif_pos small] using words ⟨i,small⟩
 · simp only [NJP_RowModel.index,dif_neg small]
   norm_num

theorem step (nodes : Nat → U8) (length : Nat) (s after : Scratch) (i w ni nw : Nat)
    (reply : Digest) (returned : Bool) (log : NJP_NativeRowCut.Log)
    (cut : NJP_NativeRowCut.Cut s i w length nodes reply after ni nw returned log)
    (words : Words s) : Words after := by
 intro k
 rw [cut.indexValues k]
 split
 · have b := index s words i
   exact lt_of_le_of_lt (Nat.div_le_self _ _) b
 · exact words k

/-- Natural scratch states are faithfully representable by the actual native
u32/usize arrays at every cut; this is proved, never a casting hypothesis. -/
theorem representable (s : Scratch) (words : Words s) (count : s.n≤9216) (cursor : s.cursor≤9216) :
 NJP_ScratchCarrier.raw (NJP_ScratchCarrier.emitted s)=s := by
 apply NJP_WriteCarrier.state_ext
 · funext k
   exact NJP_ScratchCarrier.indices_coordinate s.indices words k
 · funext k
   exact NJP_DigestCarrier.values_coordinate s.values k
 · exact NJP_WriteCarrier.small_size s.n count
 · exact NJP_WriteCarrier.small_size s.cursor cursor

#print initial
#print axioms initial
#print index
#print axioms index
#print step
#print axioms step
#print representable
#print axioms representable
end NJV_WordDomains
end
