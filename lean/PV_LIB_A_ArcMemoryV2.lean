import PV_LIB_A_StoreDispatchV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ArcMemoryV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine
open PV_LIB_A_StorePrimitiveV2 PV_LIB_A_ArcStoreV2

def atomic (ak uk : Data) (n : Nat) : Data :=
  PV_THR2_KeyValues.pack ak [PV_THR2_KeyValues.pack uk [.number n]]

def block (ik ak uk : Data) (n : Nat) (weak packet : Data) : Data :=
  PV_THR2_KeyValues.pack ik [atomic ak uk n,weak,packet]

/-- Source-selected ArcInner root, including the two atomic wrapper fields.
The carrier rebuilds this same root; neither write-definedness nor a desired
Store delta is a premise. All siblings and aggregate metadata survive. -/
theorem write_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n next : Nat) (ik ak uk weak packet : Data)
    (cell : s.cells ⟨a,i,[]⟩ = some (block ik ak uk n weak packet)) :
    writeAddress (PV_THR2_OwnInitExactReturnedCases.carrier C b) s ⟨a,i,[0,0,0]⟩
      (some (.number next)) =
      some (write s ⟨a,i,[]⟩ (some (block ik ak uk next weak packet))) := by
  unfold writeAddress
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [cell]
  rfl

theorem read_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n : Nat) (ik ak uk weak packet : Data)
    (cell : s.cells ⟨a,i,[]⟩ = some (block ik ak uk n weak packet)) :
    readAddress (PV_THR2_OwnInitExactReturnedCases.carrier C b) s ⟨a,i,[0,0,0]⟩ =
      some (.number n) := by
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [cell]
  rfl

/-- Exact boxed-cell action; local17 and the allocated ArcInner may belong to
different activations. The result follows from SOURCE CELLS and typed
references, not from the conclusion that the write already occurred. -/
theorem clone_from_cells (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (a i owner j n : Nat) (ik ak uk nk allocator weak packet : Data)
    (arcCell : s.cells ⟨a,i,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value
        (PV_THR2_KeyValues.pack nk [PV_STX2_TypedReferences.reference ⟨owner,j,[]⟩ .null]) allocator))
    (innerCell : s.cells ⟨owner,j,[]⟩ = some (block ik ak uk n weak packet)) :
    PV_THR2_LibrarySemantics_ArcClone360
      (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      [PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null] s w =
      some (write s ⟨owner,j,[]⟩
        (some (block ik ak uk ((n+1)%modulus) weak packet))) := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have selected : inner B [PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null] s w =
      some ⟨owner,j,[]⟩ := by
    apply inner_from_source B s w _ ⟨a,i,[]⟩ ⟨owner,j,[]⟩
      (PV_THR2_Packet315SourceReturn.value
        (PV_THR2_KeyValues.pack nk [PV_STX2_TypedReferences.reference ⟨owner,j,[]⟩ .null]) allocator)
      (PV_THR2_KeyValues.pack nk [PV_STX2_TypedReferences.reference ⟨owner,j,[]⟩ .null])
      (PV_STX2_TypedReferences.reference ⟨owner,j,[]⟩ .null)
    · rfl
    · change (s.cells ⟨a,i,[]⟩).bind _ = _
      rw [arcCell]
      rfl
    · rfl
    · rfl
    · rfl
  rw [clone_count B s w _ ⟨owner,j,[]⟩ n selected]
  · exact write_count C b s owner j n _ ik ak uk weak packet innerCell
  · exact read_count C b s owner j n ik ak uk weak packet innerCell

/-- Both actual emitted ArcClone tokens retain their generic metadata. -/
theorem actual12950 : PV_LIB_A_StoreDispatchV2.function
    PV_THR2_Source361PacketChildren.fn63 = some .arcClone360 := rfl

#print axioms write_count
#print axioms read_count
#print axioms clone_from_cells
#print axioms actual12950
end PV_LIB_A_ArcMemoryV2
