import NDO_JFw_Records
import NDO_JFw_PrefixForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_Prefix
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation MultiproofConeCanonical
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem inhabited : ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial =
      ok (.Ok (),expanded) ∧
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) ∧
    semanticRows 27 0 (slice JFz_RowGeometry.wire 48 6983) =
      some (pre.records.val.map (fun s => bytesOf s.val)) := by
  obtain ⟨expanded,expand,tail,root⟩ := JFw_RealExpansion.inhabited
  have flattened : bytesOf (JFw_Records.frames.map (fun s => s.val)).flatten =
      JFz_Parsed.rows00.flatten := by
    have h := congrArg List.flatten JFw_Records.bytes
    simpa only [bytesOf,List.map_flatten,List.map_map,Function.comp_def] using h
  have suffix : expanded.val.drop 32 = (JFw_Records.frames.map (fun s => s.val)).flatten :=
    MultiproofConeByteEquality.bytes_injective (tail.trans flattened.symm)
  have storedLength : (JFw_RealExpansion.stored.val.take 32).length = 32 := by
    rw [List.length_take]
    change min 32 JFw_RealExpansion.stored.length = 32
    rw [JFw_RealExpansion.stored_length]
    rfl
  have bound : 32 ≤ expanded.length := by
    have h := congrArg List.length root
    rw [storedLength,List.length_take] at h
    change 32 ≤ expanded.val.length
    omega
  obtain ⟨finish,chain,last⟩ := JFw_Chain.construct expanded _ _ JFw_Records.checked 32#usize bound suffix
  obtain ⟨old,parsed⟩ := JFw_PrefixForward.success expanded JFw_Records.frames finish bound chain last
  let pre := AspisR1PublicPreparation.PrefixAdapter.fromOld old
  have current : AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) := by
    simp only [AspisR1PublicPreparation.PrefixAdapter.parseAccepted,parsed,bind_tc_ok]
    rfl
  refine ⟨expanded,pre,expand,current,?_⟩
  have rows := PSem_SemanticRows.source_rows JFw_RealExpansion.stored JFw_RealExpansion.initial
    expanded pre expand current
  rw [JFw_RealExpansion.remaining] at rows
  exact rows

#print axioms inhabited
end AspisR1.JFw_Prefix
end
