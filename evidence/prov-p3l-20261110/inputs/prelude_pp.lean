-- PCVL_ constant bindings (recorded, CONDITIONAL_ON_BINDING): in the fresh emission the cross-crate constants
-- aspis_core::field::P and ::QM31::ZERO are external `axiom X : Result T`. They are instantiated by the gate's pure value: `ok <gate X>`.
-- This is an instantiation, not a proof about the real aspis_core items (see PCVL_HANDOFF.md, callees remaining).
def aspis_core.field.P : Result Std.U32 := ok AspisR1PublicPreparation.aspis_core.field.P
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 := ok AspisR1PublicPreparation.aspis_core.field.QM31.ZERO
