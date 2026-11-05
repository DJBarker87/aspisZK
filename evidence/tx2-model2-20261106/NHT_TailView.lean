import NHT_TailCall
import NHT_BindAssoc
set_option autoImplicit false
noncomputable section
namespace NHT_TailView
open Aeneas Aeneas.Std Result VTop_Stages
def view (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 : Result verifier.View := do
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
 ok
   { variant := AspisR1Stage2.transport.Variant.S2
     semantic := s5
     y1 := s6
     inactive := inactive
     round0 := s7
     folded_root := none
     round1 := s8
     final_message := s9
     query_bytes := s10 }

theorem source (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (a : verifier.Accumulator) :
 NHT_TailCall.run ops proof p obs inactive round0 folded round1 a =
 (do let v ← view ops proof p obs inactive round0 folded round1
     ops.op19 v p a obs) := by
 unfold NHT_TailCall.run view
 simp only [NHT_BindAssoc.source,bind_tc_ok]

/-- Only the exact View produced by these source reads requires a finish law. -/
theorem finish_packet (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (a : verifier.Accumulator)
 (packet : verifier.View → verifier.Prepared → verifier.Accumulator →
   Option (verifier.Phase → Result Unit) → Result (core.result.Result Unit verifier.Error))
 (NHM_finish : ∀ v, view ops proof p obs inactive round0 folded round1=ok v →
   ops.op19 v p a obs=packet v p a obs) :
 NHT_TailCall.run ops proof p obs inactive round0 folded round1 a =
 (do let v ← view ops proof p obs inactive round0 folded round1
     packet v p a obs) := by
 rw [source]
 apply NHT_BindOn.reached
 intro v reached
 exact NHM_finish v reached
#print axioms source
#print axioms finish_packet
end NHT_TailView
