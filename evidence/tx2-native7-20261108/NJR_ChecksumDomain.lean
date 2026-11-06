import NJO_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NJR_ChecksumDomain
open Aeneas Aeneas.Std Result AspisR1 S2W_NativeConsolidation
open MultiproofConeCanonical

def Scope (pub proof : Slice U8) : Prop := proof.val.length=57607 ∧ pub.val.length≤1880

/-- This is the actual second-call carrier derived by SourceCuts: its public
is the same encoded fixed array, not an unrestricted Slice or pointer fact. -/
theorem public_length (s : SecondCut) : s.pub.val.length=1880 := by
 change s.encoded.val.length=1880
 exact s.encoded.property

theorem of_header (s : SecondCut)
 (header : OraclePortHeader.accepts (bytesOf s.proof.val)=true) : Scope s.pub s.proof := by
 have size: s.proof.val.length=57607 := by
  simpa only [bytesOf,List.length_map] using ((OraclePortHeader.accepts_iff _).mp header).1
 exact ⟨size,by rw [public_length]⟩

/-- Caller-side scope at the SAME source call. SourceCuts is an output of
accepted_pair/cuts_of_acceptance in the headline closure, not an extra positive
root premise. Header is derived here by the actual authenticated body's guard;
no successful parser/finish or length hypothesis is supplied. The auxiliary
base/finish parameters do not form a positive root dictionary. -/
theorem of_source_cuts {F : Type} (adapter : AdapterRw.Ops) (base : VTop_Stages.Ops)
 (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
 (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
 (f : FirstCut) (s : SecondCut)
 (cuts : SourceCuts (Tx2I_Install.install adapter base finish) accounts1 accounts2 saved f s) :
 Scope s.pub s.proof := by
 let ops:=Tx2I_Install.install adapter base finish
 let D:=AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops
 have accepted : VTop_Stages.verifier.candidate.tx2_authenticated
  (Tx2I_Install.stage base finish) D s.pub s.proof s.checkpoint () none=ok (.Ok ()) := cuts.second
 obtain ⟨variant,shape,_⟩:=Tx2I_Cuts.authenticated_reached
  (Tx2I_Install.stage base finish) D () s.pub s.proof s.checkpoint none accepted
 exact of_header s (Tx2I_Install.shape_header s.proof variant shape).2.2

#print axioms public_length
#print axioms of_header
#print axioms of_source_cuts
end NJR_ChecksumDomain
