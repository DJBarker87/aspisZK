# Generated parser formatter dependency finding

The completed kernel audit queries every declaration owned by the 1378 passing
module contexts. Its 60248 structured results match 60248 full raw #print axioms
results. Exactly 72 query records, 36 in each parser Funs module, reach the 37
inherited nonstandard axiom names. All belong to the two CoreFmtDebug families.
No audited declaration outside those families reaches any of those 37 axioms.
This does not certify the blocked fresh Rc7_Top proof term.

The direct constant-reference scan DOES find two outside-family references:

- AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreCmpPartialEqError.eq
  references AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug.fmt.match_1
  (audit RPz3_587).
- AspisR1RecordParser.r1_wire.Error.Insts.CoreCmpPartialEqError.eq references
  AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug.fmt.match_1
  (audit RPz3_588).

Both match_1 declarations have no axioms. Both equality functions print exactly
[propext, Classical.choice, Quot.sound]. Lean shares a generated matcher across
these definitions; the source-token scan cannot see that generated edge.
Do not classify the entire CoreFmtDebug namespace as unreachable or delete
its compiled declarations wholesale.

Separate lead-approved cleanup candidates are the four source definitions:
AspisR1{RecordParser,PrefixAggregateParser}.r1_wire.Error.Insts.CoreFmtDebug.fmt
and AspisR1{RecordParser,PrefixAggregateParser}.r1_wire.Error.Insts.CoreFmtDebug.
Their native-decision axiom/proof helpers should disappear on regeneration.
Preserve or regenerate the shared axiom-free matchers and rebuild their equality
consumers. The formatter roots/nonstandard helpers have no outside consumers in
the checked declarations; missing sources and blocked modules remain unaudited.
No generated file was edited. The Aeneas.Std.core.fmt.Formatter library axiom is
a dependency, not a parser-owned declaration to delete from these files.

RPz3_axiom-audit.json retains all names, 70 direct edges, full nonstandard query
records and context ownership. There are 60210 distinct global names and 31
repeated global names (38 extra context occurrences), with no repeated
owner/name query. No identity of proof terms across these contexts is inferred.
All 1378 audited source import headers agree with the committed-source parser.
Fresh top reachability and its FunsExternal-to-Rust mapping remain UNKNOWN.
