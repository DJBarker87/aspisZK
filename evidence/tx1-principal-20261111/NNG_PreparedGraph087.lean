import NNG_Events087
import NNG_FinishOccurrence137
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedGraph087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
open NMT_Transport (arr)

theorem graph (env : RSL.Env) (sem : r1_semantic.Verified Unit) (v : verifier.View) (g : NMP_Emitted.Scratch) :
 observation NNG_PreparedCall087.port (NNG_Events087.events env)
  (invoke "TX1:179/Prepared_new" (sem,v,(),g)
   (NNG_PreparedCall087.call (NNG_PublicSource137.digest env) sem v () g))=
 LIB_Carriers.resultObs LIBC_PreparedLaw.port
  (LIBC_PreparedLog.events (LIBC_PreparedLaw.run (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,arr NNG_PrepareCarriers087.wide g) env).1)
  (LIBC_PreparedLaw.run (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,arr NNG_PrepareCarriers087.wide g) env).2 := by
 unfold observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,NNG_Events087.prepared_call]
 change RSL.Obs.mk (exit NNG_PreparedCall087.port (NMP_ResultTransport.outer NNG_PreparedCall087.replyBack
   (LIBC_PreparedLaw.run (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,arr NNG_PrepareCarriers087.wide g) env).2)) _=_
 generalize (LIBC_PreparedLaw.run (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,arr NNG_PrepareCarriers087.wide g) env).2=r
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>
   apply congrArg (fun value=>RSL.Obs.mk (RSL.Exit.ret value) _)
   exact NNG_PreparedCall087.reply_inverse r
#print axioms graph

theorem law (env : RSL.Env) (sem : r1_semantic.Verified Unit) (v : verifier.View) (g : NMP_Emitted.Scratch) :
 LIBC_PreparedLaw.law (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,arr NNG_PrepareCarriers087.wide g) env
 (observation NNG_PreparedCall087.port (NNG_Events087.events env)
  (invoke "TX1:179/Prepared_new" (sem,v,(),g)
   (NNG_PreparedCall087.call (NNG_PublicSource137.digest env) sem v () g))) := by
 exact Or.inl (graph env sem v g)
#print axioms law
end AspisR1.NNG_PreparedGraph087
