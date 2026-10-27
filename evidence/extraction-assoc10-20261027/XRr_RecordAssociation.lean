import XRr_SemanticCarriers
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XRr_RecordAssociation
open XRr_SemanticCarriers
/-- Complete Result transport for the actual shared record reader. -/
theorem source (p : r1_wire.Prefix) (row : U8) :
 mapR (inner id wire) (r1_wire.Prefix.record p row)=
 AspisR1PublicPreparation.r1_wire.Prefix.record (pre p) row := by
 unfold r1_wire.Prefix.record AspisR1PublicPreparation.r1_wire.Prefix.record
 unfold mapR
 split
 · rfl
 · simp only [lift,bind_tc_ok,pre]
   cases h : Array.index_usize p.records (UScalar.cast .Usize row) <;> rfl
/-- The row and framed bytes are the SAME; no validation success is assumed. -/
theorem validated (p : r1_wire.Prefix) (row : U8) :
 mapR (inner record wire) (r1_wire.Prefix.validated_record p row)=
 AspisR1PublicPreparation.r1_wire.Prefix.validated_record (pre p) row := by
 have hr := source p row
 unfold r1_wire.Prefix.validated_record AspisR1PublicPreparation.r1_wire.Prefix.validated_record
 cases h : r1_wire.Prefix.record p row with
 | fail e => simp [h,mapR] at hr; rw [←hr];rfl
 | div => simp [h,mapR] at hr; rw [←hr];rfl
 | ok r =>
   cases r with
   | Ok framed => simp only [h,mapR,bind_tc_ok,inner] at hr; rw [←hr];rfl
   | Err e => simp only [h,mapR,bind_tc_ok,inner] at hr; rw [←hr];rfl
#print axioms source
#print axioms validated
end XRr_RecordAssociation
