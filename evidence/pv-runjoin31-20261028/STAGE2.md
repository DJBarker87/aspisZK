# Semantic input stage — in progress

Checked at 44662: generic record input-leaf, nullifier and full 24-level
membership field meanings, using existing symbolic hash laws and word/public
correspondence. Checked at44663: every successful actual inner compiler has
the exact input-leaf read equal to its selected pair commitment; the recipient
read helper is also checked, without claiming its semantic obligation complete.

Witness pair fields, first path direction and first sibling are all checked in
WitnessViews31 at44671 (standard axioms, zero swap). Refusals44667–44670 did
not invoke Lean. The corrected conversion uses the actual standard function.

SemanticInput31 is an uncompiled candidate, not an accepted result. Subtraction,
zero scan, pair validation, validation reads and spendability are evidence drafts
outside the Lean tree. Native lane stage is checked through44658. No complete
InputWitnessCore.Relation, AppendBinding, recipient/sentinel conclusion,
unconditional HonestInput, owner exact coverage or V038/V045 closure is claimed.

No endpoint premise was removed, added, weakened or changed. T and the deployed
five-field P boundary remain unchanged. No shipped crates/programs changed.
