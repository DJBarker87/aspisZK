import R0.ProtocolFields
import R0.Ledger

/-! Integration and axiom audit for the corrected opening-layer theorem.
The original-kernel correspondence and uniform-query law are audited in
separate modules, without merging incompatible historical basis namespaces.
Gap 13's counterexamples concern the superseded unscaled statement only. -/

#print axioms AspisR0.Fold.F4
#print axioms AspisR0.Fold.wideF4
#print axioms AspisR0.Round.F5
#print axioms AspisR0.Round.wideF5
#print axioms AspisR0.Chord.F6
#print axioms AspisR0.Chord.wideF6
#print axioms AspisR0.Chord.interpolationLinear
#print axioms AspisR0.FibreRestoration.matched_close
#print axioms AspisR0.Opening.bad_set_cardinalities
#print axioms AspisR0.Opening.grouped_cardinalities
#print axioms AspisR0.Opening.binding
#print axioms AspisR0.Opening.wideBinding
#print axioms AspisR0.Opening.wideProtocolBinding
#print axioms AspisWide.SubfieldDescent.wideInitialCodeword_subfield_descent
