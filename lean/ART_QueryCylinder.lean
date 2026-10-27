import ARS_AccountReplay
import ARS_QueryTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueryCylinder
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def change (native : Bytes → State) (address : Bytes) (value : State) : Bytes → State :=
  fun bytes => if bytes = address then value else native bytes

theorem outside {A : Type} (p : Program Bytes State A) (native : Bytes → State)
    (address : Bytes) (value : State)
    (unissued : address ∉ (eval native p).1.map Prod.fst) :
    ARS_AccountReplay.Consistent p native (change native address value) := by
  intro bytes member
  have distinct : bytes ≠ address := by intro same; subst bytes; exact unissued member
  simp only [change,if_neg distinct]

/-- Query consistency does not instantiate the existing globally quantified
P1 record. This is a checked interface obstruction, not a soundness attack. -/
theorem no_global (native : Bytes → State) (address : Bytes) (value : State)
    (different : value ≠ native address) :
    ¬ S2W_ExtractionBoundary.P1 native (change native address value) := by
  intro p1
  have atAddress := p1.realization address
  simp only [change,if_pos rfl] at atAddress
  exact different atAddress.symm

/-- The SAME execution is unchanged at every original query while P1 fails
at one unissued address. No probability-one assertion follows from replay. -/
theorem strict {A : Type} (p : Program Bytes State A) (native : Bytes → State)
    (address : Bytes) (value : State)
    (unissued : address ∉ (eval native p).1.map Prod.fst) (different : value ≠ native address) :
    eval (change native address value) p = eval native p ∧
    ¬ S2W_ExtractionBoundary.P1 native (change native address value) :=
  ⟨ARS_AccountReplay.replay p native _ (outside p native address value unissued),
    no_global native address value different⟩

#print axioms outside
#print axioms no_global
#print axioms strict
end AspisR1.ART_QueryCylinder
end
