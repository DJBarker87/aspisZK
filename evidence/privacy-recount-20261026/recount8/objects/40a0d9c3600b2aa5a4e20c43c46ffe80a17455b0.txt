import R1Z.PV_RJDec_WorldAdequacy
import R1Z.PV_RJDec_ParserR12
import R1Z.PV_RJDec_ParserR20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserInterpret
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading PV_W_Syntax
variable [ExternalTypes] {W C : Type}
variable (dictionary : ExternalFuns)
    (a : PV_W_TypedEffects.Algebra W C Aeneas.Std.Error)
    (leaves : ∀ {B : Type} (op : PV_W_TypedEffects.Primitive B) (w : W),
      ((PV_W_TypedEffects.interpret a) op w).outcome =
        PV_W_SourceSyntax.resultOutcome ((PV_W_TypedEffects.embed op).source dictionary))
/-- Every source Result class, including every parser rejection, is retained.
The local native associations in leaves remain explicit obligations. -/
theorem terminal (bytes : Slice U8) (w : W) :
    (eval (PV_W_TypedEffects.interpret a) (PV_RJDec_ParserR20.program bytes) w).outcome =
      PV_W_SourceSyntax.resultOutcome
        (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes) := by
  rw [PV_RJDec_WorldAdequacy.typed dictionary a leaves,PV_RJDec_ParserR20.source]

theorem snapshot (bytes : Slice U8) (w : W) :
    (eval (PV_W_TypedEffects.interpret a) (PV_RJDec_ParserR12.program bytes) w).outcome =
      PV_W_SourceSyntax.resultOutcome
        (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes) := by
  rw [PV_RJDec_WorldAdequacy.typed dictionary a leaves,PV_RJDec_ParserR12.source]
#print axioms terminal
#print axioms snapshot
end R1Z.PV_RJDec_ParserInterpret
