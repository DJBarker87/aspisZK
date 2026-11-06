import NKO_HalfProofWindows
import NKO_C07Domain
import NKE_QueryInput
set_option autoImplicit false
noncomputable section
namespace NKO_IncomingCuts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
abbrev Args := NKE_QueryInput.Args
/-- EXACT required native projections. A value of this structure is not a
native certificate: every projection needs its named positive/control pair.
The proof windows remain OPEN until all fourteen prefixes and the tail pass. -/
structure Cut (before after : Args) : Prop where
 proofSize : after.proof.val.length=57607
 proofWindows : ∀ block,NKO_HalfProofWindows.Window before.proof after.proof block
 proofTail : NKO_HalfProofWindows.Tail before.proof after.proof
 prepared : NJJ_Constructors.PreparedCut before.prepared after.prepared
 accumulator : NJJ_Constructors.AccumulatorCut before.accumulator after.accumulator
 powers : ∀ i : Fin 29,after.powers.val[i.val]?=before.powers.val[i.val]?
 geometry : NKE_GeometryCuts.Cut before.geometry after.geometry
 rawSize : after.pending.raw.val.length=64
 rawCells : ∀ i,i<64 → after.pending.raw.val[i]?=before.pending.raw.val[i]?
 terms : after.pending.terms=before.pending.terms

theorem transcribe (before after : Args) (cut : Cut before after) :
 NKE_QueryInput.Cut before after :=
 ⟨cut.proofSize,NKO_HalfProofWindows.cover before.proof after.proof cut.proofWindows cut.proofTail,
 cut.prepared,cut.accumulator,cut.powers,cut.geometry,cut.rawSize,cut.rawCells,cut.terms⟩

/-- At the actual query bind all non-headline dimensions come from the source.
This auxiliary theorem leaves the reviewed native projections explicit; no
missing projection is promoted to an implementation or root premise. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation)
 (merkle : NJU_CommonObserved.Merkle) (finish : NJU_CommonObserved.Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : NJU_CommonObserved.R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : NJU_CommonObserved.Event.query proof p a g geometry pending reply∈
  (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none).events)
 (headlineSize : proof.val.length=57607) (after : Args)
 (cut : Cut ⟨proof,p,a,g,geometry,pending⟩ after) :
 after=⟨proof,p,a,g,geometry,pending⟩ := by
 obtain ⟨_,_,_,_,_,weights,raw,inverses,lines,_⟩ :=
  NKO_C07.at_actual wr rr merkle finish d pub proof ck hash proof p a g geometry pending reply entered
 exact NKE_QueryInput.same _ after headlineSize weights inverses lines raw (transcribe _ after cut)
#print axioms transcribe
#print axioms at_actual
end NKO_IncomingCuts
