import RPz7_F3U_FirstHead
set_option autoImplicit false
namespace AspisR1.F3U_OracleHead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem answer {A : Type} (p : Program Bytes State A) (H : Bytes → State)
    (address : Bytes) (state : State) (head : (eval H p).1.head?=some (address,state)) :
    state=H address := by
  cases p with
  | done value => cases head
  | ask a next =>
    have same : (a,H a)=(address,state) := Option.some.inj head
    cases same
    rfl

#print axioms answer
end AspisR1.F3U_OracleHead
