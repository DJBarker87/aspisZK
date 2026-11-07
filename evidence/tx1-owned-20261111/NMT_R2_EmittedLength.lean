import NMT_R2_EmittedData
import NMT_345Checkpoint
set_option autoImplicit false
noncomputable section
namespace NMT_R2_EmittedLength
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData
/-- Only the reached std clone field changes from the old pure-clone install. -/
def ops (keep : Bool) : AdapterRw.Ops :=
 {NGL_CheckpointModel.install baseOps with
  op35 := fun e => mapOuter toPE (clone keep (fromPE e))}

def run (keep : Bool) (a : Account) : Obs (Except ProgramError Nat) :=
 observe (fun n : Usize => n.val)
  (mapOuter (mapCore id fromPE)
   (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops keep) (toAccount a)))

theorem length_ok (keep : Bool) (a : Account) (n : Usize) (h : a.length = .Ok n) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops keep) (toAccount a) =
 .ok (.Ok n) := by
 unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len toAccount
 rw [h]
 rfl

theorem length_error (keep : Bool) (a : Account) (e : PE) (h : a.length = .Err e) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops keep) (toAccount a) =
 (do let out ← mapOuter toPE (clone keep e); .ok (.Err out)) := by
 unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len toAccount
 rw [h]
 change (do let out ← mapOuter toPE (clone keep (fromPE (toPE e))); Result.ok (core.result.Result.Err out : core.result.Result Usize OldPE)) = _
 rw [from_toPE]

/-- Full data_len law with arbitrary String-error and allocation reply. -/
theorem emitted_length (keep : Bool) (a : Account) (env : Env) :
 NMT_R2.data_len (account a) env (run keep a) := by
 unfold run NMT_R2.data_len account
 cases h : a.length with
 | Ok n => rw [length_ok keep a n h]; rfl
 | Err e =>
  rw [length_error keep a e h]
  change RS.ofCloned (.error (pe e)) env _
  unfold RS.ofCloned clone
  cases hc : (pe e).cloneAllocates <;> cases keep <;>
   simp only [hc,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true]
  · change RS.throw (pe e) env ⟨.ret (.error (pe (fromPE (toPE e)))),[]⟩
    rw [from_toPE]; rfl
  · change RS.throw (pe e) env ⟨.ret (.error (pe (fromPE (toPE e)))),[]⟩
    rw [from_toPE]; rfl
  · exact (RS.alloc_seq_iff _ env _).mpr (Or.inr rfl)
  · apply (RS.alloc_seq_iff _ env _).mpr
    left
    change RS.throw (pe e) env ⟨.ret (.error (pe (fromPE (toPE e)))),[]⟩
    rw [from_toPE]; rfl
#print axioms length_ok
#print axioms length_error
#print axioms emitted_length
end NMT_R2_EmittedLength
end
