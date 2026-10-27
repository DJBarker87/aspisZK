# Global finish recount

Rc7 specialised to the already installed FIo dictionary → FGm_Headline.deployed. Only the owner contract changes in the checked statement. No conclusion, game, event, trust item, operational slot or numerical constant changes.

|Scope|Before distinct T/P/G/C|After distinct T/P/G/C|
|---|---:|---:|
|actual antecedent|83/24/13/0|83/18/13/0|
|deployment only|6/5/0/0|6/5/0/0|
|deployment alias|0/1/0/0|0/1/0/0|
|deduplicated actual plus non-alias deployment|89/29/13/0|89/23/13/0|

Distinct delta −6P. Raw historical delta −7 rows: actual83T/26P/13G→83T/19P/13G; combined89T/31P/13G→89T/24P/13G. Quarter aliases account for the difference. Deployment rows and every native-local finish row are retained. No inherited removal is credited twice.

|Global row|Disposition|
|---|---|
|F3Y_G_L133 / Round 0: decoded read/add result is the model polynomial boundary|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L134 / Round 0: decoded multiply is quarter * decoded claim|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L135 / Round 0: decoded polynomial evaluation equals model evaluation|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L136 / Round 1: decoded read/add result is the model polynomial boundary|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L137 / Round 1: decoded multiply is quarter * decoded claim|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L138 / Round 1: decoded polynomial evaluation equals model evaluation|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|
|F3Y_G_L142 / source returned pair decodes to exact model dual-fold dot|RETAINED: source returned pair decodes to exact model dual-fold dot|
|F3Y_G_L143 / ∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j)|RETAINED: ∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j)|
|F3Y_G_L144 / first semantic polynomial boundary equals claim; under SAME EquationEndpoint view/claim/polys parsing guards|RETAINED: first semantic polynomial boundary equals claim; under SAME EquationEndpoint view/claim/polys parsing guards|
|F3Y_G_L145 / ∀ j : Fin 9, next boundary equals previous evaluation at challenge; under SAME EquationEndpoint view/claim/polys parsing guards|RETAINED: ∀ j : Fin 9, next boundary equals previous evaluation at challenge; under SAME EquationEndpoint view/claim/polys parsing guards|
|F3Y_G_L146 / last semantic evaluation equals exact masked spend terminal; under SAME EquationEndpoint view/claim/polys parsing guards|RETAINED: last semantic evaluation equals exact masked spend terminal; under SAME EquationEndpoint view/claim/polys parsing guards|
|F3Y_G_L147 / Decoded dot equals sum over all64 model final values and actual accumulator weights|REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H|

Full exact before/after/non-vacuity statements: FGm_BEFORE.lean.txt,FGm_AFTER.lean.txt,FGm_NONVACUITY.lean.txt. FGm_RC7_BEFORE.lean.txt preserves the unspecialised original. FGm_Owners.weaken proves that the old contract implies the new one on identical guards; no shape/success restriction is added to Owners. Shape is derived in the proof.

Conditional non-vacuity uses the actual new root at the same native cuts and exported successful source/runtime executions, positive zero-query margin. It retains trust,game,native acceptances,snapshots and the five remaining global laws; joint complete release non-vacuity remains open.
