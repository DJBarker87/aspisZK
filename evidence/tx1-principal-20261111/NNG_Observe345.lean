import NNG_Model345
import NMT_345RSLCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Observe345
open Aeneas Aeneas.Std NMT_345 RSL
/-- Retarget of NMT_R2_EmittedData to canonical RSL; no legacy RSL object. -/
def clone (keep : Bool) (e : PE) : Result PE :=
 if (pe e).cloneAllocates && !keep then .fail .panic else .ok e

def observe {A B : Type} (f : A → B) (r : Result (core.result.Result A PE)) :
 Obs (Except ProgramError B) :=
 match r with
 | .ok x=>⟨.ret (rustResult f x),[]⟩
 | .fail _=>⟨.abort,[]⟩
 | .div=>⟨.diverge,[]⟩

def run (keep : Bool) (a : Account) : Obs (Except ProgramError Bytes) :=
 observe (fun b : Slice U8=>b.val.map byte)
 (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (clone keep) a)

theorem data (keep : Bool) (a : Account) :
 run keep a=NNG_Pure345.cloned keep (account a).bytes := by
 unfold run NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
 simp only [account]
 cases h : a.bytes with
 | Ok b=>rfl
 | Err e=>
  change observe (fun b : Slice U8=>b.val.map byte)
   (do let err ← clone keep e; .ok (.Err err))=NNG_Pure345.cloned keep (.error (pe e))
  unfold clone NNG_Pure345.cloned
  cases hc : (pe e).cloneAllocates <;> cases keep <;>
   simp only [hc,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true] <;> rfl
#print axioms data

theorem data_law (keep : Bool) (a : Account) (env : Env) :
 OwnedAccount.data (account a) env (run keep a) := by
 rw [data]
 exact NNG_Pure345.cloned_valid keep (account a).bytes env
#print axioms data_law
end AspisR1.NNG_Observe345
