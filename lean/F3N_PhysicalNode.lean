import F3N_PhysicalCode
import Port9OR_P6Node
set_option autoImplicit false
namespace AspisR1.F3N_PhysicalNode
open Aeneas Aeneas.Std Result
open MultiproofConeRef MultiproofConePhysicalProgram
open F3N_PhysicalCode

theorem lift {A : Type} (r : Result A) :
    lower (CheckpointBytes5Effect.liftResult r)=.done r := by cases r <;> rfl

theorem conditional {A : Type} (p : Prop) [Decidable p] (yes no : SdkC_Source.Code A) :
    lower (if p then yes else no)=if p then lower yes else lower no := by split <;> rfl

theorem parent (s : reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) :
    lower (Port9OR_P6Node.parent s left right ni cursor index w)=
      writer s left right ni cursor index w := by
  simp only [Port9OR_P6Node.parent,lower,lift]
  rfl

theorem node (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    lower (Port9OR_P6Node.node s physical i w)=MultiproofConePhysicalProgram.node s physical i w := by
  simp only [Port9OR_P6Node.node,MultiproofConePhysicalProgram.node,lower,conditional,parent]

#print axioms lift
#print axioms conditional
#print axioms parent
#print axioms node
end AspisR1.F3N_PhysicalNode
