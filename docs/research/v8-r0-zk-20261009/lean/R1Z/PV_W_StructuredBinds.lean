import R1Z.PV_W_Callbacks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_StructuredBinds
open ProverRwFull PV_W_ReachedEffects
variable [ExternalTypes]

/-- Preserve a nested source do-expression as a subprogram boundary instead
of letting do-notation distribute the caller continuation into each branch. -/
def join {A B : Type} (p : P A) (k : A → P B) : P B := PV_W_Syntax.thenDo p k

theorem erase_join {A B : Type} (ops : ExternalFuns) (p : P A) (k : A → P B) :
    erase ops (join p k) = Aeneas.Std.bind (erase ops p) (fun a => erase ops (k a)) :=
  erase_bind ops p k

#print axioms erase_join
end R1Z.PV_W_StructuredBinds
