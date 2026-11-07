import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepValidate (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : Decoded V C)
 (next : Validated V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 if h : C.validateStatement s.statement = true then next ⟨s,h⟩
 else silent (.error .invalidAccountData)

theorem stepValidate_valid (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : Decoded V C)
 (next : Validated V C → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : ∀ h : C.validateStatement s.statement = true, suffix env (next ⟨s,h⟩)) :
 RS.seq (RS.check (!C.validateStatement s.statement) .invalidAccountData) suffix env
  (stepValidate V C s next) := by
 cases hv : C.validateStatement s.statement with
 | false => simp only [hv,stepValidate,Bool.false_eq_true,not_false_eq_true,dif_neg,
      Bool.not_false,RS.check,if_true,RS.seq_throw]; rfl
 | true =>
  simp only [hv,stepValidate,dif_pos,Bool.not_true,RS.check,Bool.false_eq_true,if_false,RS.seq_pure]
  exact later hv
#print axioms stepValidate_valid
end NMT_R2_345
