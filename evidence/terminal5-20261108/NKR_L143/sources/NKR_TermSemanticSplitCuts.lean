import NKR_TermDigestCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermSemanticSplitCuts
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticSource (Packed)
open NKR_TermSemanticCut (Pair)
/-- K048's replacement argument projection. Universal native coordinate
probes cover exactly these payload fields; no24cell post claim occurs here. -/
structure Arguments where
 publicArg : Option Public
 openingsArg : Openings
 selectorsArg : Selectors
 calls : Nat
 row : Nat
structure State where
 before : Packed
 after : Packed
 calls : Nat

def ArgCut (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4) (a : Arguments) : Prop :=
 a.publicArg=NKR_TermSemanticCut.pubArg pub i ∧ a.openingsArg=o ∧ a.selectorsArg=s ∧ a.calls=1 ∧ a.row=NKR_TermSemanticCut.rows i

def StateCut (before reply : Packed) (ob : State) : Prop :=
 ob.before=before ∧ ob.after=reply ∧ ob.calls=1

def joined (args : Arguments) (state : State) : NKR_TermSemanticCut.Observation :=
 ⟨args.publicArg,args.openingsArg,args.selectorsArg,state.before,state.after,state.calls,args.row⟩
/-- Two projections of the SAME named child boundary: they each observe one
call, not two calls. Source call structure fixes its stage and decoded inputs. -/
theorem compose (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4)
 (before reply : Packed) (args : Arguments) (state : State)
 (ha : ArgCut pub o s i args) (hs : StateCut before reply state) :
 NKR_TermSemanticCut.Cut pub o s i before reply (joined args state) := by
 rcases ha with ⟨p,op,sp,_,row⟩
 rcases hs with ⟨b,a,c⟩
 exact ⟨p,op,sp,b,a,c,row⟩

structure DigestArguments where
 publicArg : Public
 openingsArg : Openings
 selectorsArg : Selectors
 returned : Pair
 calls : Nat
structure DigestState where
 left : Pair
 right : Pair
 after : Packed
 calls : Nat

def DigestArgCut (pub : Public) (o : Openings) (s : Selectors) (digests : Pair) (a : DigestArguments) : Prop :=
 a.publicArg=pub ∧ a.openingsArg=o ∧ a.selectorsArg=s ∧ a.returned=digests ∧ a.calls=1

def DigestStateCut (before : Packed) (digests replies : Pair) (st : DigestState) : Prop :=
 st.left=![NJB_ArrayCarrier.cell before ⟨21,by decide⟩,NJB_ArrayCarrier.cell before ⟨22,by decide⟩] ∧
 st.right=digests ∧ st.calls=2 ∧
 ∀ j,NJB_ArrayCarrier.cell st.after j=NKR_TermSemanticCut.digestFrame before replies j

def digestJoined (a : DigestArguments) (st : DigestState) : NKR_TermSemanticCut.DigestObservation :=
 ⟨a.publicArg,a.openingsArg,a.selectorsArg,st.left,st.right,st.after,a.calls+st.calls⟩
/-- K054 replacements:250's complete2cell argument/return projection then
its two native add/write events at21/22, with a full24cell frame. -/
theorem digest_compose (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (digests replies : Pair) (a : DigestArguments) (st : DigestState)
 (ha : DigestArgCut pub o s digests a) (hs : DigestStateCut before digests replies st) :
 NKR_TermSemanticCut.DigestCut pub o s before digests replies (digestJoined a st) := by
 rcases ha with ⟨p,op,sp,_,ac⟩
 rcases hs with ⟨left,right,sc,frame⟩
 exact ⟨p,op,sp,by change a.calls+st.calls=3;rw [ac,sc],left,right,frame⟩
#print axioms compose
#print axioms digest_compose
end AspisR1.NKR_TermSemanticSplitCuts
end
