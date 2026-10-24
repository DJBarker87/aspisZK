import Port16CUT_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port16CUT_Bind
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem done_tail_length {A B : Type} (H : Bytes → State)
    (p : Program Bytes State A) (f : A → B) :
    (eval H (bind p (fun a => .done (f a)))).1.length = (eval H p).1.length := by
  rw [eval_bind]
  simp only [eval, List.append_nil]

#print axioms done_tail_length
end AspisR1.Port16CUT_Bind
end
