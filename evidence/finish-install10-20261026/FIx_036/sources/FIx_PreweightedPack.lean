import FIx_PreweightedLanes
import FIx_ArrayMeaning
import FIw_PackSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedPack
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)

def pack (v : Fin (4#usize).val → K) : K :=
  v ⟨0,by decide⟩+iBasis*v ⟨1,by decide⟩+uBasis*v ⟨2,by decide⟩+(iBasis*uBasis)*v ⟨3,by decide⟩

theorem value {N : Usize} (a : Array NQ N) (start group : Usize)
    (lanes : Array NQ 4#usize) (out : NQ) (hc : ∀ x∈a.val,Canon x)
    (run : array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
      (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
      field.QM31.ZERO (group,start,a)=ok lanes)
    (packed : field.qm31_pack_base4 (Array.to_slice lanes)=ok out) :
    Canon out ∧ decode out=pack
      (fun i=>FIx_PreweightedSelect.selected a start.val group.val i.val) := by
  have values := FIx_PreweightedLanes.value a start group lanes hc run
  have cells := FIx_ArrayMeaning.decoded_of_map lanes _ values.2
  obtain ⟨copied,same,hco,hvo⟩ := FIw_PackSource.value (Array.to_slice lanes) out
    (by exact lanes.property) values.1 packed
  have eq : copied=lanes := Subtype.ext same
  subst copied
  refine ⟨hco,?_⟩
  rw [hvo]
  change pack (FIw_ArrayValue.decoded lanes)=_
  rw [cells]
#print axioms value
end AspisR1.FIx_PreweightedPack
end
