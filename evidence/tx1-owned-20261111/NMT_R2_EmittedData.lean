import NMT_345RSLCarriers
import NMT_R2_Base
set_option autoImplicit false
noncomputable section
namespace NMT_R2_EmittedData
open Aeneas Aeneas.Std NMT_345 RSL
/-- Pinned String clone under the existing std item. `keep` is an arbitrary
allocation reply, irrelevant for variants with no heap payload. -/
def clone (keep : Bool) (e : PE) : Result PE :=
 if (pe e).cloneAllocates && !keep then .fail .panic else .ok e

def observe {A B : Type} (f : A → B) (r : Result (core.result.Result A PE)) :
 Obs (Except ProgramError B) :=
 match r with
 | .ok x => ⟨.ret (rustResult f x),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

/-- The ACTUAL fresh E003 getter, with its sole clone call interpreted by std.
All account metadata and both deferred full error payloads stay arbitrary. -/
def run (keep : Bool) (a : Account) : Obs (Except ProgramError Bytes) :=
 observe (fun b : Slice U8 => b.val.map byte)
  (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (clone keep) a)

theorem emitted_data (keep : Bool) (a : Account) (env : Env) :
 NMT_R2.data (account a) env (run keep a) := by
 unfold run NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
 unfold NMT_R2.data account
 cases a.bytes with
 | Ok b => rfl
 | Err e =>
  change RS.ofCloned (.error (pe e)) env _
  unfold RS.ofCloned clone
  cases h : (pe e).cloneAllocates <;> cases keep <;>
   simp only [h,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true]
  · rfl
  · rfl
  · exact (RS.alloc_seq_iff _ env _).mpr (Or.inr rfl)
  · exact (RS.alloc_seq_iff _ env _).mpr (Or.inl rfl)
#print axioms emitted_data
end NMT_R2_EmittedData
end
