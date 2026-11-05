import NIG_PairModel
import NIG_Slots
set_option autoImplicit false
noncomputable section
namespace NIG_PairExport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev E:=aspis_core.field.wide_exact.WideExact

def packet (r:NP6_StdModel.Reservation) (w:FIo_Install.W) (alpha:Slice E)
 (message:Slice U8) (kappa:E):Result (core.result.Result E verifier.Error):=do
 letI:=FIo_Install.allocation r
 let result←NIG_PairModel.reference (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) message (FIo_Install.toE kappa)
 match result with
 | .Ok out=>ok (.Ok (FIo_Install.fromE out))
 | .Err e=>ok (.Err (FIo_Install.error e))

theorem source (r:NP6_StdModel.Reservation) (w:FIo_Install.W) (alpha:Slice E)
 (message:Slice U8) (kappa:E):
 FIo_Install.pair r w alpha message kappa=packet r w alpha message kappa:=by
 unfold FIo_Install.pair packet
 rw [NIG_PairModel.source]

theorem NHM_pair (r:NP6_StdModel.Reservation) (p:verifier.Prepared) (v:verifier.View):
 ∀ w,(NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)→
 ∀ alpha,core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alpha→
 NHT_FinishRelationModel.PairLaw (NIG_Slots.installed r) v p w alpha
  (packet r w alpha v.final_message p.kappa):=by
 intro w new alpha range
 rw [←source]
 exact NIG_Slots.NHM_pair r p v w new alpha range
#print axioms source
#print axioms NHM_pair
end NIG_PairExport
