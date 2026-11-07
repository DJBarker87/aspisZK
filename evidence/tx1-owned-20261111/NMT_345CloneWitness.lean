import NMT_RSL_TX1_345
set_option autoImplicit false
namespace NMT_345CloneWitness
open RSL

def proofAccount : OwnedAccount :=
 ⟨B32.ofFill 0,zero32,false,false,false,.ok 58295,.ok []⟩
def publicAccount : OwnedAccount :=
 ⟨B32.ofFill 1,zero32,false,false,false,.ok 1880,.ok []⟩
def checkpointAccount : OwnedAccount :=
 ⟨B32.ofFill 2,zero32,false,true,false,.error (.borshIoError "x"),.ok []⟩
def args : TX1_345.Args :=
 ⟨zero32,[proofAccount,publicAccount,checkpointAccount],[3,10]⟩
/-- The canonical spec forces a returned String error on this OWNED input.
Whether actual std cloning admits an earlier allocation abort is a separate
source/library obligation; this lemma never assumes such an execution. -/
theorem forced_return (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V) :
 TX1_345.Ref V P C args = RS.throw (.borshIoError "x") := by
 have bad : TX1_345.badRoute args = false := by decide
 have distinct : requireDistinct [proofAccount,publicAccount,checkpointAccount] = .ok () := by rfl
 have rp : readonlyBuffer proofAccount = .ok () := rfl
 have ru : readonlyBuffer publicAccount = .ok () := rfl
 have ck : verifierCheckpoint checkpointAccount zero32 true = .error (.borshIoError "x") := by rfl
 dsimp only [args] at bad ⊢
 unfold TX1_345.Ref
 rw [bad]
 simp only [Bool.false_eq_true,if_false]
 unfold TX1_345.body
 rw [distinct,RS.ofExcept_ok,RS.seq_pure,rp,RS.ofExcept_ok,RS.seq_pure,
  ru,RS.ofExcept_ok,RS.seq_pure,ck,RS.ofExcept_error,RS.seq_throw]

theorem no_clone_abort (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V) (env : Env) :
 ¬ TX1_345.Ref V P C args env ⟨.abort,[]⟩ := by
 rw [forced_return]
 simp [RS.throw,Spec.pure]
#print axioms forced_return
#print axioms no_clone_abort
end NMT_345CloneWitness
