import PV_THR2_PacketOriginalTable
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedRetained121
open PV_STX2_Syntax
/-- Function descriptors decoded by functionId cannot be trait descriptors.
This symbolic shape fact retains arbitrary generic metadata. -/
theorem source (fn : Data) (i : Nat)
    (id : PV_THR2_OffPath.functionId fn = some i) :
    PV_THR2_SourceTraitDispatch.source fn = none := by
  unfold PV_THR2_OffPath.functionId at id
  split at id <;> first | rfl | cases id
/--121 is already a full-reply scope child in the complete retained resolver.
The joined constructor's121 disposition therefore does not change the prefix.
No returned case or descriptor exclusion for121 is required. -/
theorem child (fallback : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (id : PV_THR2_OffPath.functionId fn = some 121) :
    PV_THR2_PacketOriginalTable.table fallback fn = none := by
  have different (j : Nat) (token : Data)
      (tokenId : PV_THR2_OffPath.functionId token = some j) (neq : 121 ≠ j) : fn ≠ token := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    rw [id,tokenId] at bad
    exact neq (Option.some.inj bad)
  unfold PV_THR2_PacketOriginalTable.table
  rw [PV_THR2_PacketDataExactTable.away _ fn
    (different 124 _ rfl (by decide))
    (different 126 _ rfl (by decide))
    (different 222 _ rfl (by decide))]
  rw [PV_THR2_Source208Table.away]
  · unfold PV_THR2_OffPath.functionId at id
    split at id <;> first | (cases id; rfl) | cases id
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    rw [source fn 121 id] at bad
    cases bad
#print axioms source
#print axioms child
end PV_THR2_PacketJoinedRetained121
