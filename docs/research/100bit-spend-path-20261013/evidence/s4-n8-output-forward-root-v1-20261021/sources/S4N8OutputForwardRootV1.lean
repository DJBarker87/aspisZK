import S4P6ArrayForwardRootV1
import AspisR1FastDotsCurrentM31OpsBinding
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsN8OutputForwardRootV1
open AspisR1FastDotsCurrentM31OpsBinding (Ops withCurrentM31ParserReducer)
abbrev InnerFn := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
abbrev InnerCall := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut

theorem inner_callback_forward (base : Ops) (limbs : Array Std.U64 8#usize)
    (i : Usize) (hi : i.val<8) :
    ∃ value : Std.U32, InnerCall (withCurrentM31ParserReducer base) limbs i = .ok (value,limbs) ∧
      value.val<AspisV8R17.RawReducer.P := by
  obtain ⟨word,hr,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec limbs i (by simpa [Array.length,limbs.property] using hi))
  obtain ⟨value,hreduce,_hmod,hcanonical⟩ := AspisR1.ExtractedCurrentReducer.current_wrapper_mod word
  refine ⟨value,?_,hcanonical⟩
  simp only [InnerCall,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,
    hr,bind_tc_ok,withCurrentM31ParserReducer,hreduce]

theorem n8_array_forward (base : Ops) (limbs : Array Std.U64 8#usize) :
    ∃ values : Array Std.U32 8#usize,
      AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
        (InnerFn (withCurrentM31ParserReducer base)) limbs = .ok values ∧
      (∀ x∈values.val,x.val<AspisV8R17.RawReducer.P) := by
  apply AspisR1P6ArrayForwardRootV1.array_from_fn_forward 8#usize
    (InnerFn (withCurrentM31ParserReducer base)) (fun _ _ => True)
    (fun x => x.val<AspisV8R17.RawReducer.P) limbs (by decide) trivial
  intro current i hi _
  obtain ⟨value,hv,hcanon⟩ := inner_callback_forward base current i hi
  exact ⟨value,current,hv,hcanon,trivial⟩

#print axioms inner_callback_forward
#print axioms n8_array_forward
end AspisR1FastDotsN8OutputForwardRootV1
