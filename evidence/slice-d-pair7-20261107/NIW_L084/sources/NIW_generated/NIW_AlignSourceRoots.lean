import NIW_AlignRegularFrames
import NIW_AlignRegularUnique
import NIW_AlignFinishErase
import NIW_AlignFinishDomains
import NIW_AlignFinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignSourceRoots
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

/-- Source-observation root only. The result and log are fixed by the source
interpreter. This is not a claim that the supplied raw parent cuts have been
identified with this stream. No CLOSED clause is a hypothesis. -/
theorem regular [FIo_Native.Allocation] (w : W) (shared : Bool)
 (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers) (s : Scratch) (p : Parts)
 (s2 : w.variant=FIo_Native.transport.Variant.S2)
 (hf : NHI_TensorOuterStep.Factors w) (c0 : canonical ap0) (c1 : canonical ap1)
 (inv : NHX_RegularPost.Inv s p) :
 let execution := NIW_AlignRegularExecution.execute w alpha f ap0 ap1 (NHM_RegularKinds.kinds shared) s p
 FIo_Native.weights.process_regular_kinds w shared alpha f 2#usize 64#usize ap0 ap1 s p=execution.1 ∧
 NIW_AlignRegularStream.Ordered (NHM_RegularKinds.kinds shared) s p execution.2 execution.1 ∧
 (∀ event∈execution.2,NIW_AlignRegularStream.Clause w f ap0 ap1 event) ∧
 (∀ event∈execution.2,NIW_AlignRegularFrames.Frame event) := by
 exact ⟨NIW_AlignRegularExecution.source w shared alpha f ap0 ap1 s p,
  NIW_AlignRegularInvocation.ordered w alpha f ap0 ap1 _ s p,
  NIW_AlignRegularInvocation.clauses w alpha f ap0 ap1 s2 _ s p,
  NIW_AlignRegularFrames.all w alpha f ap0 ap1 s2 hf c0 c1 _
   (fun k hk=>NHM_RegularDomain.membership shared k hk) s p inv⟩

theorem finish (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared)
 (a : AspisR1Stage2.verifier.Accumulator) (domain : NIG_FinishInput.Domain proof v p a) :
 let execution := NIW_AlignFinishExecution.run r v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 (∀ event∈execution.2,NIW_AlignFinishInvocation.Clause r event) ∧
 (∀ event∈execution.2,NIW_AlignFinishDomains.Inputs p v a event) ∧
 NIW_AlignFinishPrefix.Prefix execution.2 :=
 ⟨NIW_AlignFinishErase.source r proof v p a domain,
  NIW_AlignFinishInvocation.clauses r proof v p a domain,
  NIW_AlignFinishDomains.all r proof v p a domain,
  NIW_AlignFinishPrefix.source r v p a⟩

#print regular
#print finish
#print axioms regular
#print axioms finish
end AspisR1.NIW_AlignSourceRoots
