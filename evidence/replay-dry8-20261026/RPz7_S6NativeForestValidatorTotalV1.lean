import RPz7_S6NativeForestHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestTotal
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

@[step] theorem lane_cast_spec (lane : U8) :
    lift (core.convert.num.FromUsizeU8.from lane) ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,trivial⟩

/-- TOTAL complete forest validator reference on both complete native variants.
Concrete payment encoders, lane-selection scan and lane-transition encoder are
installed; errors remain ordinary Rust Result values. -/
@[step] theorem validate_spec (statement : PoolV1PairForestTerminalStatementV1) :
    validate_pool_v1_pair_forest_terminal_statement_v1 statement ⦃ _ => True ⦄ := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
    pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
  step*

theorem validate_total (statement : PoolV1PairForestTerminalStatementV1) :
    ∃ result, validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (validate_spec statement)
  exact ⟨result,h⟩

#print axioms validate_total
end AspisS6NativeForestTotal
