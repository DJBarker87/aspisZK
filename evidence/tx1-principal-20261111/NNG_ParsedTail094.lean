import NNG_ProducerFull094
import NNG_PrepareTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParsedTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (digest : s.digest=NNG_PrepareTransport094.digest env)
 (observer : s.observer=none) (split : s.k.val=10)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL (NNG_PrepareTail094.args s) none)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 NNG_Reference094.prepare s env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_PrepareTree094.f_markParsed (NNG_InstalledCalls094.calls env) s)) := by
 unfold NNG_PrepareTree094.f_markParsed
 dsimp only
 rw [observer]
 change NNG_Reference094.prepare s env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind
  (invoke "verifier.mark" ((none : Option (verifier.Phase → Result Unit)),verifier.Phase.Parsed) (ok ())) _))
 rw [NNG_Silent094.invoke_ok NNG_Producer094.port env _ _ _ _
  (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))]
 unfold NNG_PrepareTree094.f_we
 change NNG_Reference094.prepare s env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind
  (invoke "aspis_core.field.wide_exact.WideExact.ZERO" () (ok (fromT3 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO))) _))
 rw [NNG_Silent094.invoke_ok NNG_Producer094.port env _ _ _ _
  (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))]
 rw [NNG_InputTransport094.zero]
 exact NNG_PrepareTail094.source env s digest observer split domain proofWidth publicWidth
#print axioms source
end AspisR1.NNG_ParsedTail094
