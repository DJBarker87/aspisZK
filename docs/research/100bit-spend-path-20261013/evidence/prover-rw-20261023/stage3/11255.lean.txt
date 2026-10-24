import R1Z.ProverRwFullFuns

/-! A concrete obstruction to an unrestricted fixed-tape interpretation of
getrandom.fill by the current pure external signature. This does not refute
privacy or an effectful / suitably proved observational refinement. -/
set_option autoImplicit false
namespace R1Z.ProverRwEntropyObstruction
open Aeneas Aeneas.Std Result ProverRwFull

def zeroInput : Slice U8 := Array.to_slice (Array.repeat 64#usize 0#u8)
def oneOutput : Slice U8 := Array.to_slice (Array.repeat 64#usize 1#u8)

theorem distinct : zeroInput ≠ oneOutput := by
  intro h
  have head := congrArg (fun s : Slice U8 => s.val.head?) h
  have bad : (0#u8) = (1#u8) := Option.some.inj head
  have value := congrArg (fun b : U8 => b.val) bad
  change 0 = 1 at value
  omega

/-- Every entropy retry starts with zeroInput again. A fixed pure dictionary
cannot return the first zero tape block and the second nonzero tape block at
that identical input. Such a two-draw tape is admitted by raw E1 sampling. -/
theorem no_two_draw_dictionary [ExternalTypes] (ops : ExternalFuns) :
    ¬ (@getrandom.fill _ ops zeroInput = ok (.Ok (),zeroInput) ∧
       @getrandom.fill _ ops zeroInput = ok (.Ok (),oneOutput)) := by
  rintro ⟨first,second⟩
  have returned := Result.ok.inj (first.symm.trans second)
  exact distinct (congrArg Prod.snd returned)

/-- A stateful two-block policy represents those same draws with no paradox:
the supplied cursor advances, even though the input buffer is identical. -/
def draw (cursor : Nat) (_ : Slice U8) : Slice U8 × Nat :=
  (if cursor=0 then zeroInput else oneOutput,cursor+1)

theorem effectful_two_draws :
    draw 0 zeroInput = (zeroInput,1) ∧ draw 1 zeroInput = (oneOutput,2) := by
  constructor <;> rfl

#print axioms distinct
#print axioms no_two_draw_dictionary
#print axioms effectful_two_draws
end R1Z.ProverRwEntropyObstruction
