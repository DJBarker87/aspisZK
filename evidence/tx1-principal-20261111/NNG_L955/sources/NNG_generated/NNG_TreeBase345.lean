import NNG_Calls345
import NMT_345PrefixFold
import NMT_345MiddleFold
import NNG_InvokeGraph328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeBase345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree

def tryCode {A : Type} (r : Result (core.result.Result A PE)) (next : A → Code Ret) : Code Ret := do
 let value ← (liftM r : Code (core.result.Result A PE))
 match value with | .Ok a=>next a | .Err e=>pure (.Err e)

theorem erase_try {A : Type} (r : Result (core.result.Result A PE)) (next : A → Code Ret) :
 erase (tryCode r next)=tryStep r (fun a=>erase (next a)) := by
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok reply=>cases reply <;> rfl
#print axioms erase_try

def prefix {W : Type} (c : Calls) (s : Selected W) (next : Decoded W → Code Ret) : Code Ret :=
 tryCode (c.c15 (selectedArray s)) fun _=>
 tryCode (c.c13 s.proofAccount) fun _=>
 tryCode (c.c13 s.publicAccount) fun _=>
 tryCode (c.c14 s.checkpointAccount s.program true) fun _=>
 tryCode (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) fun ck=>
 tryCode (c.c16 ck) fun _=>
 tryCode (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount) fun pub=>
 tryCode (c.c12 pub) fun statement=>next ⟨⟨⟨s,ck⟩,pub⟩,statement⟩

theorem erase_prefix {W : Type} (c : Calls) (s : Selected W) (next : Decoded W → Code Ret) :
 erase (prefix c s next)=prefixFold c s (fun d=>erase (next d)) := by
 unfold prefix prefixFold
 simp only [erase_try]
#print axioms erase_prefix

def middle {W : Type} (c : Calls) (s : Decoded W) (next : ProofData W → Code Ret) : Code Ret := do
 let validation ← (liftM (c.c7 s.statement) : Code _)
 tryCode (c.c2 NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError validation ()) fun _=>do
  let common ← (liftM (c.c6 s.statement) : Code _)
  let encoded ← (liftM (c.c9 common.lane_transition.candidate_afterstate) : Code _)
  tryCode (c.c2 NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError encoded ()) fun candidate=>
   tryCode (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.proofAccount) fun proof=>
    next ⟨⟨s,candidate⟩,proof⟩

theorem erase_middle {W : Type} (c : Calls) (s : Decoded W) (next : ProofData W → Code Ret) :
 erase (middle c s next)=middleFold c s (fun d=>erase (next d)) := by
 unfold middle middleFold
 simp only [Bind.bind,erase_bind,erase_lift,erase_try]
#print axioms erase_middle
end AspisR1.NNG_TreeBase345
