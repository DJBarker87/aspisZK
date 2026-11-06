import NLB_Windows
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Native C07 log-only incoming observation, carrying the retained whole
Prepared/Accumulator/powers/geometry/raw windows and KMX-disjoint byte frame.
The logical cut below is exactly NKO_FrameAtActual's accepted premises; native
ownership/capacity descriptors remain in NKO's pinned packet, not inferred here. -/
structure QueryObservation where
 written : Nat → U8
 heap : Nat → U8
 logBase : Nat
 logSize : Nat
 proofBase : Nat
 args : NKE_QueryInput.Args

/-- Reviewed projection of NKO K010–K015, K052–K059 plus retained NJJ/NJR
input windows. No child Result, output success, post-view equality, or caller
endpoint appears. Native pins/assertions are in NLB_CERTIFICATES.md. -/
def QueryCut (before : NKE_QueryInput.Args) (o : QueryObservation) : Prop :=
 before.proof.val=NKO_ReadonlyFrame.view o.heap o.proofBase before.proof.val.length ∧
 (o.proofBase+before.proof.val.length≤o.logBase ∨ o.logBase+o.logSize≤o.proofBase) ∧
 NJJ_Constructors.PreparedCut before.prepared o.args.prepared ∧
 NJJ_Constructors.AccumulatorCut before.accumulator o.args.accumulator ∧
 (∀ i : Fin 29,o.args.powers.val[i.val]?=before.powers.val[i.val]?) ∧
 NKE_GeometryCuts.Cut before.geometry o.args.geometry ∧
 o.args.pending.raw.val.length=64 ∧
 (∀ i,i<64 → o.args.pending.raw.val[i]?=before.pending.raw.val[i]?) ∧
 o.args.pending.terms=before.pending.terms

def queryArgs (before : NKE_QueryInput.Args) (o : QueryObservation) : NKE_QueryInput.Args :=
 NKO_FrameG.args o.written o.heap o.logBase o.logSize o.proofBase before o.args

def queryWindow (base : Event → Event) (observe : NKE_QueryInput.Args → QueryObservation) : Event → Event
 | .query proof p a g geometry pending _ =>
   let before : NKE_QueryInput.Args := ⟨proof,p,a,g,geometry,pending⟩
   let actual := queryArgs before (observe before)
   .query actual.proof actual.prepared actual.accumulator actual.powers actual.geometry actual.pending
     (NKO_QueryReturnG.G (NKE_QueryReturn.observed (NKE_QueryInput.child actual)))
 | e => base e
end NLB_Parent
