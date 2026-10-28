import NDO_JFw_Prefix
import NDO_JFv_PrefixRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_PrefixRecords
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open MultiproofConeCanonical

theorem source (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) : pre.records.val=JFw_Records.frames := by
  have rows := PSem_SemanticRows.source_rows JFw_RealExpansion.stored JFw_RealExpansion.initial expanded pre expand parse
  rw [JFw_RealExpansion.remaining] at rows
  have bytes : pre.records.val.map (fun s => bytesOf s.val)=JFw_Records.frames.map (fun s => bytesOf s.val) := by
    exact (Option.some.inj (rows.symm.trans JFz_Parsed.accepted00)).trans JFw_Records.bytes.symm
  have injective : Function.Injective (fun s : Slice U8 => bytesOf s.val) := by
    intro a b same
    exact Subtype.ext (MultiproofConeByteEquality.bytes_injective same)
  have undo : ∀ xs ys : List (Slice U8),
      xs.map (fun s => bytesOf s.val)=ys.map (fun s => bytesOf s.val) → xs=ys := by
    intro xs
    induction xs with
    | nil => intro ys h; cases ys <;> simp_all
    | cons a xs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons b ys =>
        have pair := List.cons.inj h
        exact congrArg₂ List.cons (injective pair.1) (ih ys pair.2)
  exact undo _ _ bytes

#print axioms source
end AspisR1.JFr_PrefixRecords
end
