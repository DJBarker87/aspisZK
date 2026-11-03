import NBP_Read
set_option autoImplicit false
noncomputable section
namespace NEQ_UnwrapDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem ok_result_state_effects {T State : Type} (copy : core.marker.Copy T)
    (value : T) (state : State) :
    (atomic_statement.unwrap_fixed_slice copy (.Ok value),state,([] : List Unit)) =
      (ok value,state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBG_Atomic.unwrap_ok copy value)

theorem err_result_state_effects {T State : Type} (copy : core.marker.Copy T)
    (error : core.array.TryFromSliceError) (state : State) :
    (atomic_statement.unwrap_fixed_slice copy (.Err error),state,([] : List Unit)) =
      (fail .panic,state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBG_Atomic.unwrap_err copy error)

/-- Actual fixed-width callers derive Ok conversion from geometry, not success. -/
theorem fixed_read_packet {N W : Usize} (bytes : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do
      let s ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
        bytes {start,«end»:=stop}
      let r ← core.array.TryFromArrayCopySlice.try_from W core.marker.CopyU8 s
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy W core.marker.CopyU8) r) =
      ok (NBP_Read.chunk bytes start.val (by omega)) :=
  NBP_Read.copy bytes start stop order bound width

#print axioms ok_result_state_effects
#print axioms err_result_state_effects
#print axioms fixed_read_packet
end NEQ_UnwrapDomains
