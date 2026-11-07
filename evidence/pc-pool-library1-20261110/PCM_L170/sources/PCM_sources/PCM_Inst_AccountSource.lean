import PCF_Payer
import PCF_Token
set_option autoImplicit false
namespace PCM_Inst_AccountSource
open Aeneas Aeneas.Std
/-- Exact CLOSED source-carrier models; PCM/RSL cell and error adapters remain
named obligations. No caller may replace this equality by an arbitrary relation. -/
abbrev PayerArgs := (Nat × Nat) × PCA.PCA_State
def payerModel (a : PayerArgs) := PCA.payerSystemReference a.1 a.2
def payerLaw (a : PayerArgs) (o : PCA.Execution Unit) : Prop := True ∧ o = payerModel a
abbrev TokenArgs := Nat × PCA.PCA_State
def tokenModel (a : TokenArgs) := PCA.tokenProgramReference a.1 a.2

def tokenLaw (a : TokenArgs) (o : PCA.Execution Unit) : Prop := True ∧ o = tokenModel a

theorem payer_graph (a : PayerArgs) (o : PCA.Execution Unit) :
    payerLaw a o ↔ True ∧ o = payerModel a := Iff.rfl

theorem token_graph (a : TokenArgs) (o : PCA.Execution Unit) :
    tokenLaw a o ↔ True ∧ o = tokenModel a := Iff.rfl

theorem payer_native (a : PayerArgs) := PCF_Payer.result_state_effects a.1 a.2
theorem token_native (a : TokenArgs) := PCF_Token.result_state_effects a.1 a.2
#print axioms payer_graph
#print axioms token_graph
#print axioms payer_native
#print axioms token_native
end PCM_Inst_AccountSource
