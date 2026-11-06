import RPv_FIx_InitialArray
import NJB_PreparedLaws
import NJB_DecodeInjective
import NJB_ArrayCarrier
import RPv_FIx_SelectedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialLaneResults
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
def cache (pr pf : NP) (i : Fin 16) : NP := if i.val<8 then pr else pf
def scalar (rate full : NQ) (i : Fin 16) : NQ := if i.val<8 then rate else full
/-- Every actual source initial-array cell is the SAME cache/opening product
observed by NJX's16lane native cut, not merely a decoded or address match. -/
theorem source (rate full : NQ) (pr pf : NP) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
 (out : Array NQ 16#usize) (hr : Canon rate) (hf : Canon full)
 (dr : NJB_PreparedLaws.Domain pr rate) (df : NJB_PreparedLaws.Domain pf full)
 (ho : FIw_ArrayValue.canonical o.z)
 (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  field.QM31.ZERO (pr,o,pf)=ok out) :
 ∀ i : Fin 16,field.PreparedQm31Multiplier.mul (cache pr pf i) (NJB_ArrayCarrier.cell o.z i)=ok (NJB_ArrayCarrier.cell out i) := by
 have value:=FIx_InitialArray.value rate full pr pf o out hr hf dr df ho run
 have decoded:=FIx_ArrayMeaning.decoded_of_map out _ value.2
 intro i
 have hs : Canon (scalar rate full i) := by unfold scalar;split <;> assumption
 have hd : NJB_PreparedLaws.Domain (cache pr pf i) (scalar rate full i) := by unfold cache scalar;split <;> assumption
 obtain ⟨q,cq,hq,vq⟩ := NJB_PreparedLaws.mul_result (cache pr pf i) (scalar rate full i) (NJB_ArrayCarrier.cell o.z i) hs (NJB_ArrayCarrier.canonical_cell o.z ho i) hd
 have eq : q=NJB_ArrayCarrier.cell out i := by
  apply NJB_DecodeInjective.qm _ _ hq (NJB_ArrayCarrier.canonical_cell out value.1 i)
  rw [vq]
  change decode (scalar rate full i)*decode (NJB_ArrayCarrier.cell o.z i)=FIw_ArrayValue.decoded out i
  rw [decoded,FIx_SelectedMeaning.read o.z i.val i.isLt]
  rfl
 simpa only [eq] using cq
#print axioms source
end AspisR1.NKI_InitialLaneResults
end
