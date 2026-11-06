import NJL_PatternOuter
import NJL_PatternMeaning
import NJB_PatternArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PatternRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJB_PatternArray (state patterns selectors pack)
/-- Positive complete raw4-array root with both native-cut invocation traces
and the exact sparse basis meaning. No inner Result, endpoint equality, Run,
operation dictionary or independent decoded array is a root input. -/
theorem source (values : Array NQ 4#usize) (weights : Array NQ 26#usize) (terms : Array NQ 14#usize)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights) (ht : FIw_ArrayValue.canonical terms) :
 ∃ after,NJL_PatternOuter.Trace (patterns terms) (selectors weights) (List.ofFn (fun g : Fin 4=>g)) (state values) after ∧
 NJB_PatternArray.reference values weights terms=ok (pack after) ∧ FIw_ArrayValue.canonical (pack after) ∧
 (∀ g,decode (state (pack after) g)=decode (state values g)+
 NJL_PatternMeaning.dot (fun i=>decode (patterns terms i)) (fun i=>decode (selectors weights i)) g) := by
 have cp : ∀ i,Canon (patterns terms i) := fun _=>NJB_ArrayCarrier.canonical_cell terms ht _
 have cw : ∀ i,Canon (selectors weights i) := fun _=>NJB_ArrayCarrier.canonical_cell weights hw _
 have cv : ∀ i,Canon (state values i) := fun _=>NJB_ArrayCarrier.canonical_cell values hv _
 obtain ⟨after,call,trace,ha⟩ := NJL_PatternOuter.source (patterns terms) (selectors weights) (state values) cp cw cv
 obtain ⟨other,otherCall,_,otherValue⟩ := NJB_PatternReference.result (patterns terms) (selectors weights) (state values) cp cw cv
 have same : after=other := Result.ok.inj (call.symm.trans otherCall)
 have value := (congrArg (fun s=>NJB_StateUpdates.decoded s) same).trans otherValue
 refine ⟨after,trace,?_,?_,?_⟩
 · simp only [NJB_PatternArray.reference,call,bind_tc_ok]
 · exact NJB_ArrayCarrier.canonical_array _ (fun _=>ha _)
 · intro g
   rw [NJB_PatternArray.state_pack]
   exact (congrFun value g).trans (NJL_PatternMeaning.value _ _ _ g)
#print source
#print axioms source
end AspisR1.NJL_PatternRoot
end
