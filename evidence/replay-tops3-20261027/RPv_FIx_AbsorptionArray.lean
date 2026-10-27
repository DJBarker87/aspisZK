import RPv_FIx_Absorption
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_AbsorptionArray
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIx_Absorption

theorem value (low fixed two eight nodes : NQ) (o out : Array NQ 16#usize)
    (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (ho : ∀ x∈o.val,Canon x)
    (run : pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal low fixed two eight nodes o=ok out) :
    (∀ x∈out.val,Canon x) ∧ out.val.map decode=List.ofFn
      (fun i : Fin (16#usize).val=>decode low*blocks (decode fixed) (decode two)
        (decode eight) (decode nodes) i.val*FIv_NativeArray.value o i.val) := by
  unfold pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal array_from_fn_copy at run
  apply FIx_Builder.fromFn (16#usize) callback Canon decode (fun n=>decode low*blocks (decode fixed) (decode two) (decode eight) (decode nodes) n*FIv_NativeArray.value o n) (fixed,two,eight,nodes,low,o) out _ run
  intro i hi result last called
  exact callback_value low fixed two eight nodes o i result last hl hf ht he hn ho called

#print axioms value
end AspisR1.FIx_AbsorptionArray
end
