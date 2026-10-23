import S2J_Invocation
import S2J_SliceEquality
import S2F_Sequence

set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2Trust S2H S2E_Reference.S2E_Reference

/-- Value semantics of the native guard; slice equality includes exact length. -/
def guard1 (data : Slice U8) (count : Usize) : Bool :=
  decide ((data = (Array.make 2#usize [3#u8,10#u8]).to_slice ∨
    data = (Array.make 2#usize [3#u8,11#u8]).to_slice) ∧ count = 3#usize)

theorem shape1_port (ops : S2E_Reference.Ops) (data : Slice U8) (count : Usize) :
    shape1 (installEquality ops) data count = ok
      (if guard1 data count then .Ok () else .Err
        solana_program_error.ProgramError.InvalidInstructionData) := by
  unfold shape1
  simp only [installEquality, sliceArrayEq, byte_equality, bind_tc_ok]
  by_cases a : data = (Array.make 2#usize [3#u8,10#u8]).to_slice <;>
    by_cases b : data = (Array.make 2#usize [3#u8,11#u8]).to_slice <;>
    by_cases c : count = 3#usize <;> simp [guard1,a,b,c]

def nativeGuard {W : Type} (observe : W → NativeArguments) (_ : S2F.Step) (n : W) :
    S2F.Outcome solana_program_error.ProgramError W :=
  if guard1 (observe n).instruction (observe n).accountCount then .next n
  else .error .InvalidInstructionData n

/-- Executes the actual extracted shape1, retaining outer failure/div as abort. -/
def referenceGuard {Child Alloc Event : Type} (ops : S2E_Reference.Ops)
    (_ : S2F.Step) (r : OwnedCut Child Alloc Event) :
    S2F.Outcome solana_program_error.ProgramError (OwnedCut Child Alloc Event) :=
  match shape1 (installEquality ops) r.instruction (alloc.vec.Vec.len r.sdk.accounts) with
  | .ok (.Ok ()) => .next r
  | .ok (.Err e) => .error e r
  | .fail _ => .abort r
  | .div => .abort r

/-- Both branches preserve the complete extended relation: cut1 neither writes
memory nor acquires any guard. Includes invalid instruction/count rejections. -/
theorem cut1_stepLaw {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (observe : W → NativeArguments)
    (fixed : FixedInvocation) (o : Originals W Child Alloc Event)
    (ops : S2E_Reference.Ops) :
    S2F.StepLaw (InvocationRelated L observe fixed) (nativeGuard observe)
      (referenceGuard ops) o .shape1 := by
  intro n r related
  unfold nativeGuard referenceGuard
  rw [shape1_port,related.nativeInstruction,related.count]
  split <;> simp only [Bool.true_eq,↓reduceIte] <;> constructor <;> exact related

#print axioms shape1_port
#print axioms cut1_stepLaw
end AspisR1.S2J
