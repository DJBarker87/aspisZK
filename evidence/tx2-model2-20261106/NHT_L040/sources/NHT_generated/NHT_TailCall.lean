import NHT_CommonCuts
set_option autoImplicit false
noncomputable section
namespace NHT_TailCall
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
/-- The exact post-flush proof views. Offsets remain the installed emitted
constants. No successful slice read or finish is assumed. -/
def run (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (a : verifier.Accumulator) : Result (R Unit) := do
 let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
 let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
 let s7 ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof {start:=round0,«end»:=folded}
 let final ← ops.op21
 let s8 ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof {start:=round1,«end»:=final}
 let openings ← ops.op20
 let s9 ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof {start:=final,«end»:=openings}
 let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
 ops.op19 {variant:=AspisR1Stage2.transport.Variant.S2,semantic:=s5,y1:=s6,
   inactive:=inactive,round0:=s7,folded_root:=none,round1:=s8,final_message:=s9,
   query_bytes:=s10} p a obs

/-- Actual Vec writeback and the SAME flush output, preserving all other fields. -/
theorem after_query (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (out : Slice aspis_core.field.QM31)
 (flush : ops.op9 pending a.weights.deref=ok out) :
 NHQ_Tx2CommonModel.afterQuery ops proof p obs inactive round0 folded round1 (.Ok (a,pending)) =
 run ops proof p obs inactive round0 folded round1 {a with weights:=⟨out.val,out.property⟩} := by
 change (do let output ← ops.op9 pending a.weights.deref
            run ops proof p obs inactive round0 folded round1
              {a with weights:=⟨output.val,output.property⟩})=_
 rw [flush]
 rfl
#print axioms after_query
end NHT_TailCall
