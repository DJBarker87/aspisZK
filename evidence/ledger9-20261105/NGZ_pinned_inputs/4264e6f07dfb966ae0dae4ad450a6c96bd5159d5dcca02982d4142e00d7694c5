import Lean
import NGE_NEL_DigestLoopFrame
import NFY_Part053
import RPz7_S2K_DigestBytes

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_DigestInstance
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder AspisR1.S2K

/-- The count and returned word of the SAME cursor consumed by the emitted
byte-step theorem. No independently selected index or word is a premise. -/
theorem next_call (d : Array U32 8#usize) (i : Usize) (bound : i.val < 8) :
    DigestTotal.next (DigestTotal.cursor d i) = ok
      (some (i,d.val[i.val]'(by have := d.property; change d.val.length=8 at this; omega)),
       DigestTotal.cursor d (Usize.ofNatCore (i.val+1) (by scalar_tac))) :=
  DigestTotal.next_row d i bound

/-- Instantiate the accepted decreasing-suffix induction and cohort identity
at the same raw digest; arbitrary external state is preserved by this pure call. -/
theorem result_and_frame {State : Type} (d : Array U32 8#usize) (state : State) :
    (AspisR1AdapterReconstruct.aspis_statement.atomic_statement.encode_digest_canonical d,
       state) = (ok (DigestBytes.bytes d),state) := by
  rw [NFY_NED_DigestCohorts.digest_encode, DigestBytes.exact]

#print axioms next_call
#print axioms result_and_frame
end NGE_NEM_DigestInstance

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
