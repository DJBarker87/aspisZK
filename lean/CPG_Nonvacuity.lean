import CPG_Game
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPG_Game CPP_BankState Hist_RuntimeEntry

variable {A : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Bank) (record : Record) (saved : alloc.vec.Vec U8) (actions : List (Action A))

/-- An operational, adjacent two-transaction model. No accepting cryptographic
fixture is claimed. Arbitrary source actions are actually evaluated, not
replaced by an empty trace or a desired checkpoint equality. -/
def canonical : Observations Bool A where
  bank := fun t => if t then
    (CPP_BankHistory.run n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached initial) 0 saved) actions).1 else initial
  layout := fun _ => ⟨fun _ => (0,0),fun _ => record,fun _ => 0,fun _ => 0⟩
  next := fun t u => t = false ∧ u = true
  intervening := fun _ _ => []
  parentReply := fun _ => .ok (.Ok ())
  copied := fun _ => saved
  actions := fun _ => actions

theorem game :
    let p := canonical n1 n2 copy allocator id initial record saved actions
    DeployedPairExecution p false true (entry p false) (entry p true) saved actions := by
  refine ⟨⟨⟨rfl,rfl⟩,rfl,rfl⟩,⟨rfl,rfl,?_⟩,rfl,⟨rfl,rfl⟩⟩
  exact List.not_mem_nil

theorem RuntimePersistence (system : S2W_ExtractionBoundary.Program) :
    let p := canonical n1 n2 copy allocator id initial record saved actions
    CPR_DataPersistence.TwoTransactionLaw (adjacent p) (ordinary p system) (before p)
      (tentative p n1 n2 copy allocator id) (success p) (loaded p) := by
  dsimp only
  intro t u linked key eligible
  have ht : t = false := linked.1.1
  have hu : u = true := linked.1.2
  subst t
  subst u
  rfl

/-- Nonempty suffixes remain nonempty in the physical checkpoint projection. -/
theorem nonempty (action : Action A) (rest : List (Action A)) :
    let p := canonical n1 n2 copy allocator id initial record saved (action :: rest)
    (result p n1 n2 copy allocator id false).2 ≠ [] := by
  exact List.cons_ne_nil _ _

#print axioms game
#print axioms RuntimePersistence
#print axioms nonempty
end AspisR1.CPG_Nonvacuity
end
