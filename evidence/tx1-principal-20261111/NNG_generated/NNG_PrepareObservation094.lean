import NNG_PrepareTransport094
import NNG_FinishOccurrence137
import NNG_Events087
import NNG_TypedEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareObservation094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136
open NNG_Carriers094
abbrev Observer:=Option (verifier.Phase → Result Unit)
abbrev Scratch:=Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev Args:=aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public × Slice U8 × Unit × Observer × Scratch

def prepareEvents (env : RSL.Env) (args : Args) : List RSL.Event:=
 (run (NNG_Tree087.tree (NNG_PrepareEmission087.calls env)
   (NNG_PrepareAdapter094.input (NNG_PrepareTransport094.digest env) args.1 args.2.1 () args.2.2.2.1 args.2.2.2.2))).2.flatMap (NNG_Events087.events env)
def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event:=
 NNG_TypedEvents.select "TX1:087/prepare" (prepareEvents env) event

theorem prepare_call {Reply : Type} (env : RSL.Env) (args : Args) (reply : Result Reply) :
 events env (.call "TX1:087/prepare" args reply)=prepareEvents env args := by
 simp [events,NNG_TypedEvents.select]
#print axioms prepare_call

theorem exact (a : NNG_PrepareInput087.Args) (env : RSL.Env) :
 observation NNG_PrepareTransport094.port (events env)
  (invoke "TX1:087/prepare" (fromT9 a.public_,NNG_Data137.bytes a.proof,(),(none : Observer),arr fromT3 a.g)
   (NNG_PrepareAdapter094.call env (NNG_PrepareTransport094.digest env) (fromT9 a.public_)
    (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)))=
 NNG_Producer087.producer a none env := by
 unfold observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,prepare_call]
 rw [NNG_PrepareTransport094.call]
 unfold prepareEvents
 rw [NNG_PrepareTransport094.input]
 unfold NNG_Producer087.producer
 generalize NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a none env)=r
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>
  apply congrArg (fun out=>RSL.Obs.mk (RSL.Exit.ret out) _)
  exact NNG_PrepareTransport094.output r
#print axioms exact
end AspisR1.NNG_PrepareObservation094
