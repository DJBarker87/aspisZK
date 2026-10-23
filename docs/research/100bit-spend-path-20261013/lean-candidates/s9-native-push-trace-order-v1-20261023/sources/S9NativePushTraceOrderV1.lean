import S9NativePushRangeTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativePushTraceOrderV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativePushRangeTraceV1
open AspisR1S9PushByteProductsReaderCallsV1 (Iter Dot)

/-- Reuse the actual already-extracted push trace: no second loop inversion
or independent index sequence is introduced. -/
theorem trace_indices_order (bytes : Slice U8) (scratch : Slice aspis_core.field.QM31)
    (n : Usize) (iter : Iter) (dot out : Dot) (js : List Usize)
    (htrace : Trace bytes scratch n iter dot js out) :
    js.map (fun j => j.val)=List.range' iter.start.val js.length := by
  induction htrace with
  | done it dot hend hat => simp only [List.map_nil,List.length_nil,List.range'_zero]
  | @step it next dot mid out j js w q hn hj hw hr hq hp ht ih =>
    obtain ⟨he,hlt,hstep,hend⟩ :=
      AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds it next j hn
    have hv : j.val=it.start.val := congrArg (fun x : Usize => x.val) he
    have hstart : next.start.val=it.start.val+1 := by omega
    rw [List.map_cons,List.length_cons,ih,List.range'_succ,hv,hstart]

/-- Every operand's actual source index is within the SAME byte field count. -/
theorem trace_indices_bounded (bytes : Slice U8) (scratch : Slice aspis_core.field.QM31)
    (n : Usize) (iter : Iter) (dot out : Dot) (js : List Usize)
    (htrace : Trace bytes scratch n iter dot js out) :
    ∀ j ∈ js, j.val<n.val := by
  induction htrace with
  | done => simp
  | @step it next dot mid out j js w q hn hj hw hr hq hp ht ih =>
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with he | hk
    · subst k;exact hj
    · exact ih k hk

#print axioms trace_indices_order
#print axioms trace_indices_bounded
end AspisR1S9NativePushTraceOrderV1
