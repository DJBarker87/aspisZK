import LIBB_ObservationFold
import LIBB_ObservationValues
import LIB_Bytes
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2Auth
open Aeneas Aeneas.Std AspisR1
attribute [local instance] Classical.propDecidable
/-- Carrier validity only; Dom064 implies this without any new clause. -/
def Fits (pub proof ck : RSL.Bytes) : Prop :=
 pub.length≤Usize.max ∧ proof.length≤Usize.max ∧ ck.length≤Usize.max

/-- Canonical source model on byte arguments, including the named C04 abort
prefixes. No native execution witness defines this law. -/
def law (pub proof ck : RSL.Bytes) : RSL.Spec (Except LIBB_V2Carriers.VErr Unit) :=
 if h : Fits pub proof ck then LIBB_ObservationModel.law
  (LIB_Bytes.fromBytes pub h.1) (LIB_Bytes.fromBytes proof h.2.1) (LIB_Bytes.fromBytes ck h.2.2)
 else RSL.Spec.panic

def value (pub proof ck : RSL.Bytes) (env : RSL.Env) : Except LIBB_V2Carriers.VErr Unit :=
 if h : Fits pub proof ck then LIBB_EnvValues.evaluator env
  (LIB_Bytes.fromBytes pub h.1) (LIB_Bytes.fromBytes proof h.2.1) (LIB_Bytes.fromBytes ck h.2.2)
 else .error .Checkpoint

theorem same (pub proof ck : Slice U8) :
 law (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck)=
 LIBB_ObservationModel.law pub proof ck := by
 unfold law
 rw [dif_pos ⟨LIB_Bytes.bytes_bound pub,LIB_Bytes.bytes_bound proof,LIB_Bytes.bytes_bound ck⟩]
 rw [LIB_Bytes.from_bytes,LIB_Bytes.from_bytes,LIB_Bytes.from_bytes]

theorem returns (pub proof ck : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (law pub proof ck) env (value pub proof ck env) := by
 unfold law value
 split
 · exact LIBB_ObservationModel.returns _ _ _ _
 · intro o r observed returned
   change o=⟨.abort,[]⟩ at observed
   subst o
   cases returned

theorem writeFree (pub proof ck : RSL.Bytes) : RSL.TAS.WriteFree (law pub proof ck) := by
 unfold law
 split
 · exact LIBB_ObservationValues.writeFree _ _ _
 · intro env o observed cell bytes
   change o=⟨.abort,[]⟩ at observed
   subst o
   exact List.not_mem_nil

/-- Exact Dom064 remains the original four clauses. -/
theorem fits_of_domain (pub proof ck : RSL.Bytes)
 (domain : LIBB_Tx2Domain.domain pub proof ck) : Fits pub proof ck := by
 obtain ⟨hp,hc,hu,_⟩:=domain
 refine ⟨?_,?_,?_⟩
 · have bound : 1880≤Usize.max := by decide
   exact hu.trans bound
 · rw [hp]
   decide
 · rw [hc]
   decide

/-- The resolved graph's rev3 Functional gate reads the same reservation
binder as the full source law. Independent abort arms are retained by law. -/
def resolved (pub proof ck : RSL.Bytes) : RSL.Spec (Except LIBB_V2Carriers.VErr Unit) :=
 if h : Fits pub proof ck then LIBB_EnvValues.graph
  (LIB_Bytes.fromBytes pub h.1) (LIB_Bytes.fromBytes proof h.2.1) (LIB_Bytes.fromBytes ck h.2.2)
 else RSL.Spec.panic

theorem resolved_functional (pub proof ck : RSL.Bytes) : RSL.Spec.Functional (resolved pub proof ck) := by
 unfold resolved
 split
 · exact LIBB_EnvValues.functional _ _ _
 · intro env
   exact ⟨⟨.abort,[]⟩,fun _=>Iff.rfl⟩
/-- Canonical byte-carrier transport of the full observation fold. The
runtime Bound064 premise is representation, never added to Dom064. -/
theorem native {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (domain : LIBB_Tx2Domain.domain (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck))
 (outcome : NLW_Full064.End (LIBB_PartitionEnv.H env)
  (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : NLW_Full064.Args Unit))
 (events : List (NLW_Full064.Event Ambient Unit))
 (invocation : NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ outcome events)
 (bound : LIBB_ObservationFold.Bound064 env pub proof ck outcome) (trace : NNC_DigestTrace.Trace)
 (source : NNC_ObservedWeak.TraceOf outcome trace) :
 NLW_Full064.Law (LIBB_PartitionEnv.H env) _ outcome ∧
 events=NLW_Full064.chronology (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ outcome ∧
 law (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome,NNC_DigestTrace.render trace⟩ := by
 have own:=(LIBB_Tx2Domain.native env pub proof ck).mp domain
 have closed:=(NMN_064.root (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ own).1 outcome events invocation
 refine ⟨closed.1,closed.2,?_⟩
 rw [same]
 exact LIBB_ObservationFold.tx2 env pub proof ck world own outcome events invocation bound trace source
#print axioms native
#print axioms same
#print axioms returns
#print axioms writeFree
#print axioms fits_of_domain
#print axioms resolved_functional
end LIBB_Tx2Auth
end
