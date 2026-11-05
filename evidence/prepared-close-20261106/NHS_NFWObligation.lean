import NHS_PrepareFields
import NHS_PrepareScratch
import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_NFWObligation
open Aeneas Aeneas.Std Result
/-- The literal NGC boundary, instantiated on the adopted DrvC dictionary.
No replacement preparation operation or abstract owner contract is introduced. -/
theorem source {F C : Type} (base : DrvC_Installation.Configuration F C) :
 NGC_PreparationBoundary.NFW_Obligation (DrvC_Dictionary.ops (F3V_Install.configuration base)) := by
 intro H D pub proof hash scratch p g _parsed _scan success
 change DrvC_Program.mapResult DrvC_Dictionary.prepareReply
   (AspisR1CurrentCaller.verifier.candidate.prepare
     (DrvC_Installation.currentInstalled (F3V_Install.configuration base))
     (AspisS6CurrentFirstInstallation.toDigest D) (AspisS6CurrentVerifierCarrier.toPublic pub)
     proof hash none (Tx1Q_Carriers.arr Tx1Q_Carriers.unE scratch))=ok (.Ok p,g) at success
 unfold DrvC_Program.mapResult at success
 obtain ⟨reply,prepare,last⟩ := NFW_Invert.bind _ _ _ success
 rcases reply with ⟨r,rs⟩
 cases r with
 | Err e => cases last
 | Ok out =>
   have same := Prod.mk.inj (Result.ok.inj last)
   have preparedSame := core.result.Result.Ok.inj same.1
   cases preparedSame
   cases same.2
   constructor
   · exact NHS_PrepareFields.installed
       (DrvC_Installation.current (F3V_Install.configuration base)) base.boundaries base.std
       (AspisS6CurrentFirstInstallation.toDigest D) hash (AspisS6CurrentVerifierCarrier.toPublic pub)
       proof _ rs out prepare
   · exact NHS_PrepareScratch.source
       (DrvC_Installation.current (F3V_Install.configuration base))
       (F3M_CircleSource.install base.boundaries) base.std
       (AspisS6CurrentFirstInstallation.toDigest D) hash (AspisS6CurrentVerifierCarrier.toPublic pub)
       proof out _ rs prepare
#print axioms source
end AspisR1.NHS_NFWObligation
