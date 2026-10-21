import MultiproofConeKeyAdapters
import MultiproofConeSlices

set_option autoImplicit false
namespace AspisR1.MultiproofConeOpeningAdapters
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices OraclePortSelectedDraft
open AspisV8R19.DuplexFrames

/-- Exact checked physical opening view at the frozen byte offset. The wire
carrier equality is retained explicitly; it is not a decoder/caller proof. -/
theorem opening_view (proof : Slice U8) (length : proof.val.length=57607)
    (p : OraclePortCompactDraft.Parsed) (wire : p.wire=bytesOf proof.val)
    (pos : Nat) (bound : pos<22) :
    ∃ start finish view,
      start.val=10055+pos*832 ∧ finish.val=start.val+832 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=start,«end»:=finish}=ok view ∧
      view.val.length=832 ∧ bytesOf view.val=opening p pos := by
  let start : Usize := UScalar.ofNat (10055+pos*832) (by scalar_tac)
  let finish : Usize := UScalar.ofNat (10055+pos*832+832) (by scalar_tac)
  have sv : start.val=10055+pos*832 := by simp [start]
  have fv : finish.val=start.val+832 := by simp [finish,sv]
  have order : start.val≤finish.val := by omega
  have fit : finish.val≤proof.val.length := by omega
  refine ⟨start,finish,sub proof start finish,sv,fv,range_total _ _ _ order fit,?_,?_⟩
  · rw [sub_length proof start finish order fit];omega
  · rw [bytes_sub]
    simp only [opening,wire,sv,fv,Nat.add_sub_cancel_left]

/-- Flattened address observed by batch_leaf for each of the three reached
kinds. Each interval is relative to the exact 832-byte opening above. -/
def leafAddress (kind : Nat) (b : Bytes) : Bytes :=
  if kind=0 then [0x10,0x71] ++ b.take 480 ++ OraclePortCompactDraft.slice b 608 32
  else if kind=1 then [0x10,0xf1] ++ OraclePortCompactDraft.slice b 480 128 ++ OraclePortCompactDraft.slice b 640 32
  else [0x10,0x72] ++ OraclePortCompactDraft.slice b 672 128 ++ OraclePortCompactDraft.slice b 800 32

theorem leaf_address (p : OraclePortCompactDraft.Parsed) (kind pos : Nat) :
    leafAddress kind (opening p pos)=leaf p kind pos := by
  unfold leafAddress leaf BinMerkle32Leaf.leafInput
  split <;> (try split) <;> simp [List.append_assoc]

/-- Source key decoding followed by opening selection is exactly the frozen
leaf address, without an index-injectivity or duplicate consistency premise. -/
theorem selected_leaf (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (mem : pos∈OraclePortFrozenOrder.sortedPositions q batch kind) :
    leafAddress kind (opening p ((if batch=0 then 0 else 10)+
      (MultiproofConeSortOrder.packed q batch kind pos).val%256)) = leaf p kind pos := by
  rw [MultiproofConeKeyAdapters.packed_opening q batch kind pos
    (MultiproofConeKeyAdapters.sorted_member q batch kind pos mem)]
  exact leaf_address p kind pos

#print axioms opening_view
#print axioms leaf_address
#print axioms selected_leaf
end AspisR1.MultiproofConeOpeningAdapters
