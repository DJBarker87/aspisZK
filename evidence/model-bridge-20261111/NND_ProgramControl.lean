import NND_Returned
import NND_AccountCarrier
set_option autoImplicit false
namespace NND_ProgramControl
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
abbrev P (A : Type) := Result (core.result.Result A solana_program_error.ProgramError)

def tryThen {A B : Type} (r : P A) (k : A → P B) : P B := do
 let out ← r
 match out with | .Ok a => k a | .Err e => ok (.Err e)

/-- Complete emitted Try protocol, including outer fail/div and every
ProgramError payload. This is the source operator, with no successful-child
premise or free operation law. -/
theorem source_try {A B : Type} (r : P A) (k : A → P B) :
 (do let out ← r
     let cf ← core.result.Result.Insts.CoreOpsTry.branch out
     match cf with
     | core.ops.control_flow.ControlFlow.Continue a => k a
     | core.ops.control_flow.ControlFlow.Break e =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        B (core.convert.FromSame solana_program_error.ProgramError) e) = tryThen r k := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok v => cases v <;> rfl

/-- A local composition lemma only: concrete caller proofs discharge hk by
named child transports, never expose it as an A1/A2 root premise. -/
theorem transport {A B X Y : Type} (r : core.result.Result A solana_program_error.ProgramError)
 (k : A → P B) (f : A → X) (g : B → Y) (F : X → Except RSL.ProgramError Y)
 (hk : ∀ a, outer (reply g) (k a) = ok (F (f a))) :
 outer (reply g) (tryThen (ok r) k) = ok (NND_Returned.ebind (reply f r) F) := by
 cases r with
 | Err e => rfl
 | Ok a => exact hk a

#print axioms source_try
#print axioms transport
end NND_ProgramControl
