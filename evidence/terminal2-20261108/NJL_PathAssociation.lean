import NJL_PathPacket
import NJL_OccupancyAssociation
import RPv_FIx_PathMeaning
import NDO_JFy_PathLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathAssociation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_PathPacket (Openings Packet pack)
open NJL_OccupancyPacket (cell)
theorem value (selector : NQ) (o : Openings) (p : Packet selector o) :
 FIw_ArrayValue.decoded (pack p.after)=FIx_PathMeaning.coefficients (decode selector)
  (FIv_NativeArray.value o.z 0) (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z) := by
 funext i
 rw [NJL_PathPacket.pack_decode,p.value]
 fin_cases i <;>
  simp [NJL_PathFrame.value,NJL_PathFrame.look,p.selected_value,p.empty_value,p.head_value,
   NJL_OccupancyAssociation.cell_value,FIx_PathMeaning.coefficients] <;> ring
/-- Positive17-cell root: the complete native invocation record is constructed
internally and equals the adopted emitted literal on the SAME openings.
Canonical bit is arbitrary; no binary-bit condition or child-result premise. -/
theorem source (selector : NQ) (o : Openings) (hs : Canon selector)
 (hz : FIw_ArrayValue.canonical o.z) (hb : FIw_ArrayValue.canonical o.succ_z) :
 ∃ p : Packet selector o,NJL_PathPacket.reference selector o=ok (pack p.after) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.path_lanes_literal selector o=ok (pack p.after) ∧
 FIw_ArrayValue.canonical (pack p.after) := by
 obtain ⟨p,call,canonical⟩ := NJL_PathPacket.source selector o hs hz hb
 obtain ⟨old,oldCall,oldCanonical⟩ := WP.spec_imp_exists (JFy_PathLiteral.source selector o hs hz hb)
 have oldValue := FIx_PathMeaning.value selector o old hs hz hb oldCall
 have same := NJL_ArrayCodec.ext (pack p.after) old canonical oldCanonical ((value selector o p).trans oldValue.2.symm)
 exact ⟨p,call,by rw [same];exact oldCall,canonical⟩
#print Packet
#print source
#print axioms value
#print axioms source
end AspisR1.NJL_PathAssociation
end
