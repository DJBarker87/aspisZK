import NDO_JHn_LiteSavedIdentity
import NDO_JHc_QueryPost
import RPz7_Tx1Q_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_LiteReturnedIdentity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
variable [sha : JHn_ByteSHA]
/-- Every successful candidate return on the retained inputs has the retained
checkpoint bytes. The preparation/query/flush are extracted from THAT return. -/
theorem source (saved : alloc.vec.Vec U8)
    (returned : verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved)) :
    saved.val=JFx_NativeBytes.checkpoint.val := by
  obtain ⟨split,parsed,zero,p,scratch,shape,scan,z,prep,tail⟩ :=
    Tx1Reachability.tx1_success installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () saved returned
  obtain ⟨initial,root,g,pending,out,after,flushed,init,batch,geo,pend,query,flush,write⟩ :=
    Tx1Q_Cuts.suffix installed digest JFx_NativeBytes.publicInput JFx_NativeBytes.proof
      10#usize () p scratch saved tail
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p _ scratch prep
  obtain ⟨out2,after2,flushed2,query2,flush2,next,size,variant,rhs,power⟩ :=
    JHc_QueryPost.source p _ scratch initial pending g prep queries init pend geo
  have eqQuery : (out2,after2)=(out,after) :=
    core.result.Result.Ok.inj (Result.ok.inj (query2.symm.trans query))
  obtain ⟨eo,ea⟩ := Prod.mk.inj eqQuery
  subst out2
  subst after2
  have ef : flushed2=flushed := Result.ok.inj (flush2.symm.trans flush)
  subst flushed2
  exact JHn_LiteSavedIdentity.source p _ scratch initial out pending after g flushed saved
    prep init pend geo query flush variant next size write
#print axioms source
end AspisR1.JHn_LiteReturnedIdentity
end
