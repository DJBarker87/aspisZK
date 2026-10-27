# Native-local ledger delta on the actual top

Baseline Rc9_Top.deployed; successor FIs_Top.deployed. The complete statements
are FIs_BEFORE.lean.txt and FIs_AFTER.lean.txt; FIs_statement-check.json checks
that only theorem/result names differ. No input hypothesis, quantifier,
carrier, runtime item, failure event, numeric constant, or other conclusion
changes. FIs_Result exports the original native Witness/Calls, not an
additional Shape/Aux contract. The continuation is strictly stronger.

| Row | Closed native-local predicate | Same-run derivation |
|---|---|---|
| L133 | round0 boundary | FIs_OnRun -> FIn_FromRead.rounds -> FIn_Round.laws |
| L134 | round0 quarter | same RoundLaws derivation at installed quarter |
| L135 | round0 evaluation | same literal parser/data and physical slice read |
| L136 | round1 boundary | same native witness and installed dictionary |
| L137 | round1 quarter | same derivation; predicate aliases L134 |
| L138 | round1 evaluation | same literal parser/data and physical slice read |
| L147 | final-message dot | SAME saved writer/reader decode -> saved64 -> FIn_WeightLength.twelve -> SAG_ShapeDot.value |

FIs_Caller derives SAME proof/checkpoint bytes from reached tx2 facts.
FIs_Literal decodes the SAME saved writer result. FIs_Cons_Second derives
Calls/Aux/Shape together from the actual native second call, and the copied
FIs_ source factory retains that witness through every continuation.
FIs_Result consumes those internally derived facts before returning the
new result. They are not supplied as new headline premises.

Raw actual83T/19P/13G ->83T/12P/13G; combined non-alias89T/23P/13G
->89T/16P/13G. Distinct actual83T/18P/13G ->83T/12P/13G;
distinct combined89T/22P/13G ->89T/16P/13G. Delta0T/-7 rawP/0G/0C,
or0T/-6 distinctP/0G/0C. Deployment4P and T/G/C unchanged.
FIs_recount.py preserves the immutable Rc9 row identities, guards, scopes
and owners; it removes precisely these seven rows. No source-global row
receives credit again. Remaining native-local Pair, matching and three
semantic endpoints stay separate from their five source-global counterparts.
