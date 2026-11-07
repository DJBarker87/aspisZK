import NMC_ErrorExit
import NLU_TerminalTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers NMC_Parent
/-- Actual256 full outer/inner Result transport at exactly the parent-owned
claims and the actual alpha/original challenges. Both Err mapping and cleanup
are composed before observing the parent; no NLI provisional RowSpec is used.
Canonicality inputs here are LOCAL helper obligations, never leftover136
root premises about a child's output. -/
theorem installed {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (heap : Heap) (identity : Nat)
 (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
 (challenges : r1_wire.Challenges) (domain : NLU_Terminal.InputDomain pub challenges)
 (hc : ∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row)
 (ha : FIw_ArrayValue.canonical (mapArray toQ alpha)) :
 NMC_Exit.public allocator state heap identity (NLU_Terminal.nativeTerminal pub claims alpha challenges)=
 NMC_Exit.public allocator state heap identity (FIq_Terminal.terminal pub claims alpha challenges) := by
 exact congrArg (NMC_Exit.public allocator state heap identity)
   (NLU_Terminal.installed pub claims alpha challenges domain hc ha)
#print axioms installed
set_option pp.proofs false in #print installed
end AspisR1.NMC_Terminal
end
