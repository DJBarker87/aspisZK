import CuSavingsGammaTx1
set_option autoImplicit false
namespace AspisR1.CuSavingsGammaSourceBinding
open Aeneas Aeneas.Std Result AspisR1CuGamma
open CuSavingsGammaTable

/-- A source block with one immutable gamma-table binder at its boundary.
The source checker binds `tail` to the identical entire remaining Rust block.
Its semantics is arbitrary; it may return errors or diverge. -/
inductive Block where
  | tail (tokens : List String)
  | powers29 (next : Block)

/-- Shared immutable arrays have their value interpretation, as in Aeneas.
Only the leading immutable binder is interpreted here. No tail statement is
removed, reordered, evaluated or assumed successful. -/
def execute {A : Type} (tail : List String → Table → Result A)
    (powers : E → Result Table) (gamma : E) (table : Table) : Block → Result A
  | .tail code => tail code table
  | .powers29 body => do
      let computed ← powers gamma
      execute tail powers gamma computed body

theorem introduce_binder {A : Type} (tail : List String → Table → Result A)
    (powers : E → Result Table) (gamma : E) (initial : Table) (body : Block) :
    execute tail powers gamma initial (.powers29 body) =
      (do let computed ← powers gamma
          execute tail powers gamma computed body) := by rfl

#print axioms introduce_binder
end AspisR1.CuSavingsGammaSourceBinding
