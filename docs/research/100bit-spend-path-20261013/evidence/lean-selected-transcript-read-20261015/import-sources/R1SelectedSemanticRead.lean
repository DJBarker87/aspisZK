import R1FinOptionSequence

/-! Collect the 25 strict semantic payloads from indexed transcript records.
This connects byte parsing to SemanticPayloadView's dependent input type;
challenge recovery and accepted-transcript correspondence remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedSemanticRead

abbrev Payloads := (row : Fin 25) → SemanticRecordCodec.RowPayload row

def read (rs : List InitialWalk.RawRec) : Option Payloads :=
  FinOptionSequence.sequence SemanticRecordCodec.RowPayload
    (fun row => SelectedPrefixRead.readAt rs row.val (SemanticRecordCodec.decode row))

theorem read_eq_some_iff (rs : List InitialWalk.RawRec) (p : Payloads) :
    read rs = some p ↔ ∀ row : Fin 25,
      SelectedPrefixRead.readAt rs row.val (SemanticRecordCodec.decode row) =
        some (p row) :=
  FinOptionSequence.sequence_eq_some_iff _ _ p

theorem read_append_stable (rs tail : List InitialWalk.RawRec)
    (h : 24 < rs.length) : read (rs ++ tail) = read rs := by
  unfold read
  congr 1
  funext row
  exact SelectedPrefixRead.readAt_append_stable rs tail row.val _ (by omega)

#print axioms read_eq_some_iff
#print axioms read_append_stable

end AspisR1.SelectedSemanticRead
end
