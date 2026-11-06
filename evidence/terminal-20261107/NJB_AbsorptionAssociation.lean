import NJB_Absorption
import NJB_DecodeInjective
import NJB_ArrayReads
import NDO_JFy_AbsorptionBuilder
import RPv_FIx_AbsorptionArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_AbsorptionAssociation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
/-- Exact complete raw-array Result equality with the adopted emitted literal
helper. Its totality and every callback value/frame clause are discharged. -/
theorem result (low fixed two eight nodes : NQ) (opened : Array NQ 16#usize)
 (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
 (ho : FIw_ArrayValue.canonical opened) :
 NJB_Absorption.reference low fixed two eight nodes opened=
 pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal low fixed two eight nodes opened := by
 obtain ⟨a,ra,ca,va⟩ := NJB_Absorption.result low fixed two eight nodes opened hl hf ht he hn ho
 obtain ⟨b,rb,cb⟩ := WP.spec_imp_exists (JFy_AbsorptionBuilder.source low fixed two eight nodes opened hf ht he hn hl ho)
 have vb := FIx_AbsorptionArray.value low fixed two eight nodes opened b hl hf ht he hn ho rb
 have sameModel :
  (fun lane : Fin 16=>NJB_AbsorptionLane.literal (decode low) (decode fixed) (decode two)
   (decode eight) (decode nodes) (decode (NJB_Absorption.cell opened lane)) lane)=
  (fun lane : Fin 16=>decode low*FIx_Absorption.blocks (decode fixed) (decode two)
   (decode eight) (decode nodes) lane.val*FIv_NativeArray.value opened lane.val) := by
  funext lane
  rw [NJB_ArrayReads.value opened lane.val (by rw [opened.property,NJB_Absorption.size];exact lane.isLt)]
  rfl
 have equalValues : a.val.map decode=b.val.map decode := by
  rw [va,vb.2]
  simp only [NJB_Absorption.size]
  exact congrArg (fun f : Fin 16 → K=>List.ofFn f) sameModel
 have same := NJB_DecodeInjective.array a b ca cb equalValues
 rw [ra,rb,same]
#print result
#print axioms result
end AspisR1.NJB_AbsorptionAssociation
end
