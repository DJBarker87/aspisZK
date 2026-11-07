import NLP_Assembly
import NLP_C04Chronology
import NLP_C04Reply
import NLB_Transition
set_option autoImplicit false
noncomputable section
namespace NLT_ParentCuts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
/-- A single C07 observation is associated with the entered call, rather than
an unrelated total function on all possible query inputs. These are the
reviewed input/frame clauses, NOT a proof that an arbitrary native capture
satisfies them. No parent root is claimed by this module. -/
structure Query (before : NKE_QueryInput.Args) where
 observation : NLB_Parent.QueryObservation
 frame : NLB_Parent.QueryCut before observation
/-- Site-indexed allocator replies. Each is the complete Reservation (including
failure); equality of outcomes at different sites is deliberately absent.
Association to the actual allocator remains an obligation of the native cut. -/
inductive AllocationSite where
 | resume | pending | finish
 deriving DecidableEq
structure Allocation where
 site : AllocationSite
 reservation : NP6_StdModel.Reservation
/-- Chronological native-cut data and SAME caller continuation. There is no
free global observe function. A query capture can only be consumed at its
own decoded query arguments. This is an auxiliary relation until its native
cut interpretation is installed, not a replacement for that interpretation. -/
inductive Cut : Event → Event → Type where
 | resume (ck proof pub : Slice U8) (seed reply : R (verifier.Prepared × verifier.Accumulator))
   (allocation : Allocation) (site : allocation.site=.resume) :
   Cut (.resume ck proof pub seed) (.resume ck proof pub reply)
 | powers (gamma : aspis_core.field.wide_exact.WideExact)
   (seed reply : Result (Array aspis_core.field.wide_exact.WideExact 29#usize)) :
   Cut (.powers gamma seed) (.powers gamma reply)
 | inactive (bytes : Slice U8) (seed reply : Result (Option aspis_core.field.wide_exact.WideExact)) :
   Cut (.inactive bytes seed) (.inactive bytes reply)
 | merkle (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
   (seed reply : R Unit) : Cut (.merkle proof p folded seed) (.merkle proof p folded reply)
 | geometry (queries : Array U32 22#usize) (next : Usize)
   (seed reply : R verifier.QueryGeometry) : Cut (.geometry queries next seed) (.geometry queries next reply)
 | pending (weights : Slice aspis_core.field.QM31) (seed reply : R verifier.BatchedWeights)
   (allocation : Allocation) (site : allocation.site=.pending) :
   Cut (.pending weights seed) (.pending weights reply)
 | query (before : NKE_QueryInput.Args) (seed reply : R (verifier.Accumulator × verifier.BatchedWeights))
   (capture : Query before) :
   Cut (.query before.proof before.prepared before.accumulator before.powers before.geometry before.pending seed)
    (.query before.proof before.prepared before.accumulator before.powers before.geometry before.pending reply)
 | flush (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31)
   (seed reply : Result (Slice aspis_core.field.QM31)) : Cut (.flush pending weights seed) (.flush pending weights reply)
 | finish (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) (seed reply : R Unit)
   (allocation : Allocation) (site : allocation.site=.finish) (locations : NIW_AlignFinishComposed.Locations) :
   Cut (.finish v p a seed) (.finish v p a reply)
end NLT_ParentCuts
