import NHV_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NID_TailView
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 MultiproofConeSlices

def exactView (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact) : verifier.View :=
 {variant:=.S2,semantic:=Array.to_slice (Std.Array.empty U8),
  y1:=Array.to_slice (Std.Array.empty U8),inactive:=inactive,
  round0:=sub proof 7527#usize 7751#usize,folded_root:=none,
  round1:=sub proof 7783#usize 8007#usize,
  final_message:=sub proof 8007#usize 10055#usize,
  query_bytes:=Array.to_slice (Std.Array.empty U8)}

/-- Instantiate the exact source constructor on the SAME original proof.
No independent View, arbitrary canonical windows or successful finish input. -/
theorem produced (ops : VTop_Stages.Ops) (proof : Slice U8) (p : verifier.Prepared)
 (inactive : aspis_core.field.wide_exact.WideExact) (bound : 10055≤proof.val.length) :
 NHT_TailView.view (NHT_Tx2CommonModel.constants ops) proof p none inactive
  7527#usize 7751#usize 7783#usize=ok (exactView proof inactive) := by
 have r0 := range_total proof 7527#usize 7751#usize (by decide) (by change 7751≤proof.val.length;omega)
 have r1 := range_total proof 7783#usize 8007#usize (by decide) (by change 8007≤proof.val.length;omega)
 have rf := range_total proof 8007#usize 10055#usize (by decide) bound
 simp only [NHT_TailView.view,NHT_Tx2CommonModel.constants,lift,bind_tc_ok,
  NHT_Offsets.final,NHT_Offsets.openings,r0,r1,rf]
 rfl

theorem fields (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact) :
 (exactView proof inactive).variant=.S2 ∧
 (exactView proof inactive).round0.val=(proof.val.drop 7527).take 224 ∧
 (exactView proof inactive).round1.val=(proof.val.drop 7783).take 224 ∧
 (exactView proof inactive).final_message.val=(proof.val.drop 8007).take 2048 ∧
 (exactView proof inactive).folded_root=none := by
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem widths (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (bound : 10055≤proof.val.length) :
 (exactView proof inactive).round0.val.length=224 ∧
 (exactView proof inactive).round1.val.length=224 ∧
 (exactView proof inactive).final_message.val.length=2048 := by
 have w := NHV_TailWindows.widths proof bound
 exact ⟨w.2.1,w.2.2.2.1,w.2.2.2.2⟩
#print axioms produced
#print axioms fields
#print axioms widths
end NID_TailView
