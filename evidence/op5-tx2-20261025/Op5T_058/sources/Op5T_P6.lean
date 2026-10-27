import Op5T_Concrete
import OraclePortFrozenOrderSlotPath
import Op5I_AcceptedCarrierCounterexample
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_P6
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeRef MultiproofConePhysicalProgram MultiproofConePhysicalDigest MultiproofConePhysicalTransport
open MultiproofConeP6Callbacks MultiproofConeP6Batch MultiproofConeP6Frozen2Stage

/-- One actual compression query; its continuation consumes the oracle reply. -/
def parent : Parent := fun left right => .ask (parts left right) .done

/-- All callback/leaf gates are discharged by their concrete programs.
Only the primitive digest interpretation remains. This is a P6 program
instance, not a proof that an arbitrary SDK child port executes this program. -/
theorem boundary {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (rawOracle H input)) :
    P6Boundary D hash H parent parent parent referenceLeaf := by
  refine ⟨oracle,?_,?_,?_,?_⟩
  · intro left right; rfl
  · intro left right; rfl
  · intro left right; rfl
  · intro p q kind pos s room; rfl

/-- A canonical batch's own reads cannot contain Op5I's fabricated answer.
This statement covers acceptance and rejection, and arbitrary body inputs. -/
theorem no_fabricated_read (H : Bytes → State)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (nodes : Nat → Nat → Slice U8) (batch : Nat) (s : reference.Scratch)
    (a : Bytes) (d : State) (bad : d ≠ H a) :
    (a,d) ∉ (eval H (sourceBatch parent parent referenceLeaf p q nodes batch s)).1 := by
  intro member
  have law := Op5I_AcceptedCarrierCounterexample.evaluated_reply H
    (sourceBatch parent parent referenceLeaf p q nodes batch s) (a,d) member
  exact bad law

#print axioms boundary
#print axioms no_fabricated_read
end AspisR1.Op5T_P6
end
