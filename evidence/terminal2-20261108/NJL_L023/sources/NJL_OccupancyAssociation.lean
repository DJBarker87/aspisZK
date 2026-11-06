import NJL_OccupancyPacket
import NJL_ArrayCodec
import RPv_FIy_OccupancyMeaning
import NDO_JFy_OccupancyLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyAssociation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_OccupancyPacket (Packet cell pack)
theorem cell_value (a : Array NQ 16#usize) (i : Fin 16) :
 decode (cell a i)=FIv_NativeArray.value a i.val := by
 exact (NJB_ArrayReads.value a i.val (by rw [a.property,NJB_Absorption.size];exact i.isLt)).symm
/-- Symbolic factorization on arbitrary canonical occupied; no bit condition. -/
theorem value (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
 (p : Packet input output expected opened) :
 FIw_ArrayValue.decoded (pack p.last)=FIy_OccupancyMeaning.model (decode input) (decode output)
  expected.val (FIv_NativeArray.value opened) := by
 funext i
 rw [NJL_OccupancyPacket.pack_decode,p.last_value,p.middle_value]
 rw [congrFun p.head_value (Fin.cast NJL_OccupancyPacket.size12 i)]
 fin_cases i <;>
  simp [NJL_OccupancyHead.model,NJL_OccupancyFrame.value,NJL_OccupancyFrame.sourceIndex,
   p.one_value,p.both_value,p.selected_value,p.empty_value,cell_value,
   FIy_OccupancyMeaning.model,FIy_OccupancyPrefix.model,FIy_OccupancyTail.scalar,
   Function.update,Fin.ext_iff] <;> ring
/-- Positive composed root: derived invocation and its native cuts, SAME full
returned array, canonicality and exact complete adopted cohort Result. -/
theorem source (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
 (hi : Canon input) (ho : Canon output) (he : expected.val<FIw_ScalarArithmetic.P)
 (ha : FIw_ArrayValue.canonical opened) :
 ∃ p : Packet input output expected opened,
 NJL_OccupancyPacket.reference input output expected opened=ok (pack p.last) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal input output expected opened=ok (pack p.last) ∧
 FIw_ArrayValue.canonical (pack p.last) := by
 obtain ⟨p,call,canonical⟩ := NJL_OccupancyPacket.source input output expected opened hi ho he ha
 obtain ⟨old,oldCall,oldCanonical⟩ := WP.spec_imp_exists
  (JFy_OccupancyLiteral.source input output expected opened hi ho he ha)
 have oldValue := FIy_OccupancyMeaning.value input output expected opened old hi ho he ha oldCall
 have same := NJL_ArrayCodec.ext (pack p.last) old canonical oldCanonical ((value input output expected opened p).trans oldValue.2.symm)
 exact ⟨p,call,by rw [same];exact oldCall,canonical⟩
#print Packet
#print source
#print axioms cell_value
#print axioms value
#print axioms source
end AspisR1.NJL_OccupancyAssociation
end
