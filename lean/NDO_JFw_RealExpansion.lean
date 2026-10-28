import NDO_JFw_Entry
import NDO_JFz_Parsed
import RPz7_PSem_Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_RealExpansion
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation MultiproofConeCanonical
open AspisV8R19.DuplexFrames OraclePortCompactDraft

def stored : Slice U8 :=
  ⟨(JFx_NativeBytes.proof.val.drop 16).take 7015, by
    have small := JFx_NativeBytes.proof.property
    simp only [List.length_take,List.length_drop]
    omega⟩

def initial : Slice U8 :=
  ⟨List.replicate 13831 0#u8,by simp only [List.length_replicate];scalar_tac⟩

theorem stored_length : stored.length = 7015 := by
  change ((JFx_NativeBytes.proof.val.drop 16).take 7015).length = 7015
  have length : JFx_NativeBytes.proof.val.length = 57607 := JFx_NativeBytes.proofBytes_length
  rw [List.length_take,List.length_drop,length]
  rfl

theorem initial_length : initial.length = 13831 := by
  change (List.replicate 13831 (0#u8)).length = 13831
  exact List.length_replicate

theorem remaining : bytesOf (stored.val.drop 32) = slice JFz_RowGeometry.wire 48 6983 := by
  simp only [stored,List.drop_take,List.drop_drop,bytesOf,List.map_take,List.map_drop,
    slice,JFz_RowGeometry.wire]

theorem inhabited : ∃ expanded : Slice U8,
    compact.expand_semantic nativeValues stored initial = ok (.Ok (),expanded) ∧
    bytesOf (expanded.val.drop 32) = JFz_Parsed.rows00.flatten ∧
    expanded.val.take 32 = stored.val.take 32 := by
  obtain ⟨expanded,call⟩ := JFw_Entry.success stored initial stored_length initial_length
  obtain ⟨rows,parsed,bytes⟩ := PSem_Expansion.source_rows stored initial expanded call
  rw [remaining] at parsed
  have same : rows = JFz_Parsed.rows00 := Option.some.inj
    (parsed.symm.trans ((PSem_Rows.strict_iff _ _ _ _).mp JFz_Parsed.accepted00).2)
  subst rows
  exact ⟨expanded,call,bytes,PSem_Root.take_of_prefix stored expanded
    (AspisS1NativeCompactBodyFrame.semantic_root_prefix nativeValues stored initial expanded call)⟩

#print axioms stored_length
#print axioms initial_length
#print axioms remaining
#print axioms inhabited
end AspisR1.JFw_RealExpansion
end
