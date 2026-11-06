import NKO_FrameG
set_option autoImplicit false
noncomputable section
namespace NKO_FrameAtActual
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
/-- Source-side (y)(3) instantiation of the log-only incoming frame G at C07.
All widths are derived internally except the headline's own proof width.
The ABI input view/disjoint live borrows are retained native-cut interpretation;
no post-view or child-success equation is assumed. Not a positive parent root. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : Event.query proof p a g geometry pending reply∈
  (run wr rr merkle finish d pub proof ck hash none).events)
 (headlineSize : proof.val.length=57607)
 (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (inputView : proof.val=NKO_ReadonlyFrame.view heap proofBase proof.val.length)
 (disjoint : proofBase+proof.val.length≤logBase ∨ logBase+logSize≤proofBase)
 (observed : NKE_QueryInput.Args)
 (prepared : NJJ_Constructors.PreparedCut p observed.prepared)
 (accumulator : NJJ_Constructors.AccumulatorCut a observed.accumulator)
 (powers : ∀ i : Fin 29,observed.powers.val[i.val]?=g.val[i.val]?)
 (geometryCut : NKE_GeometryCuts.Cut geometry observed.geometry)
 (rawWidth : observed.pending.raw.val.length=64)
 (rawCells : ∀ i,i<64 → observed.pending.raw.val[i]?=pending.raw.val[i]?)
 (terms : observed.pending.terms=pending.terms) :
 NKE_QueryInput.child (NKO_FrameG.args written heap logBase logSize proofBase
  ⟨proof,p,a,g,geometry,pending⟩ observed)=
 NJJ_Common.query proof p a g none geometry pending 22#usize := by
 obtain ⟨_,_,_,_,_,weights,raw,inverses,lines,_⟩ :=
  NKO_C07.at_actual wr rr merkle finish d pub proof ck hash proof p a g geometry pending reply entered
 have same := NKO_FrameG.args_source written heap logBase logSize proofBase
  (⟨proof,p,a,g,geometry,pending⟩ : NKE_QueryInput.Args) observed inputView disjoint
  headlineSize weights inverses lines raw prepared accumulator powers geometryCut rawWidth rawCells terms
 rw [same]
 rfl
#print source
#print axioms source
end NKO_FrameAtActual
