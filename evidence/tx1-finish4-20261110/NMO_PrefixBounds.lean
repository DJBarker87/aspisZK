import NMC_RecordAtState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_PrefixBounds
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The original own-argument provenance supplies all 27 record extents;
no successful finish/claims reply or chosen replacement Prefix is assumed. -/
theorem record_lengths {H : Type} (input : NLU.Input H)
 (domain : NLU.InputDomain input) (row : Fin 27) :
 (FJb_TailCell.cell input.prefix1.records row).val.length ≤ 3717 := by
 obtain ⟨bytes,pre,parsed,same⟩ := domain.parsedPrefix
 rw [same]
 change (FJb_TailCell.cell pre.records row).val.length ≤ 3717
 rw [NIX_PredecessorFrames.aggregate bytes pre parsed row]
 exact (NGX_PrefixGeometry.widths row.val).2
/-- The frozen parser's source geometry fits the independently offset native
views. This is a bound, not a native pointer/layout correspondence theorem. -/
theorem native_windows (row : Fin 27) :
 NGX_PrefixGeometry.start row.val ≤ 57575 ∧
 NGX_PrefixGeometry.width row.val ≤ 57575 - NGX_PrefixGeometry.start row.val := by
 have start := NGX_PrefixGeometry.start_bound row.val (by omega)
 have width := NGX_PrefixGeometry.widths row.val
 omega
#print axioms record_lengths
#print axioms native_windows
set_option pp.proofs false in #print record_lengths
set_option pp.proofs false in #print native_windows
end AspisR1.NMO_PrefixBounds
end
