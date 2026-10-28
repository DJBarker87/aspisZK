import R1Z.PV_W_TypedEffects
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_WorldAdequacy
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading PV_W_Syntax
variable [ExternalTypes] {W C A : Type}
/-- Local source-value adequacy is required at every world. Worlds and calls
remain arbitrary; this is not a native purity or silence premise. -/
theorem typed (dictionary : ExternalFuns)
    (a : PV_W_TypedEffects.Algebra W C Aeneas.Std.Error)
    (leaves : ∀ {B : Type} (op : PV_W_TypedEffects.Primitive B) (w : W),
      ((PV_W_TypedEffects.interpret a) op w).outcome =
        PV_W_SourceSyntax.resultOutcome ((PV_W_TypedEffects.embed op).source dictionary))
    (p : PV_W_TypedEffects.P A) (w : W) :
    (eval (PV_W_TypedEffects.interpret a) p w).outcome =
      PV_W_SourceSyntax.resultOutcome (PV_W_TypedEffects.erase dictionary p) := by
  induction p generalizing w with
  | pure v => rfl
  | failure e => rfl
  | diverge => rfl
  | call op k ih =>
    cases h : (PV_W_TypedEffects.embed op).source dictionary with
    | ok v =>
      simpa only [eval,PV_W_Threading.bind,leaves,h,PV_W_SourceSyntax.resultOutcome,
        PV_W_TypedEffects.erase,PV_W_SyntaxMap.mapOps,PV_W_SourceSyntax.erase,Aeneas.Std.bind]
        using ih v ((PV_W_TypedEffects.interpret a) op w).world
    | fail e =>
      simp only [eval,PV_W_Threading.bind,leaves,h,PV_W_SourceSyntax.resultOutcome,
        PV_W_TypedEffects.erase,PV_W_SyntaxMap.mapOps,PV_W_SourceSyntax.erase,Aeneas.Std.bind]
    | div =>
      simp only [eval,PV_W_Threading.bind,leaves,h,PV_W_SourceSyntax.resultOutcome,
        PV_W_TypedEffects.erase,PV_W_SyntaxMap.mapOps,PV_W_SourceSyntax.erase,Aeneas.Std.bind]
#print axioms typed
end R1Z.PV_RJDec_WorldAdequacy
