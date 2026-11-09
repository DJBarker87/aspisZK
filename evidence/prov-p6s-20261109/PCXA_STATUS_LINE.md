# PCXA status line for the next ledger

Target not yet established. The ledger job consumes PCXA_PROVENANCE.json; no ledger row was edited.

Provenance status (P6 snapshot PCXA_, first of two P6 runs; ledger30 base 6ce07a6a593; frozen 4bb3b3f; Target not yet established). HEADLINE CONE AspisR1.TAS_FinalB.deployed_splitB (146370 constants): 209 emitted gate modules reached; module rollups {'OPEN': 155, 'EQUALITY_PROVED': 5, 'RECEIPTED': 40, 'NO_ANNOTATED_DEFINITION_REACHED': 9}; 1612 reached annotated definitions: 258 RECEIPTED, 435 EQUALITY_PROVED, 4 EQUALITY_DOMAIN (loop-return refinements only), 915 OPEN (547 no fresh emission, 247 wrong-basis records counted OPEN under the 2026-11-09 ruling, 81 failed/other, 40 no equality record). CLOSED-row view (599 rows): 471 rows conditional at definition level, 114 clean at definition level, 12 reach no emitted module, 2 rootless; 562 rows rely on a module whose rollup is OPEN (module-level, conservative; PCO gave 565 rows relying on any non-receipted module). Lean audit: 493 of 493 credited theorem names audited in 11 successful scopes with only propext/Classical.choice/Quot.sound (985 PRVEq constants), one bundle scope (L006) failed and was replaced. Hand models: 245 hand-written gate models (191 matched by a deployed_splitB cone constant), no trust row added. Not covered here: release replay, L187/L188, source-to-ELF; R22 owns checked-vs-wrapping and is not discharged by provenance.

Counts source: PCXA_PROVENANCE.json summary; deployed_splitB cone first, ledger30 CLOSED-root view for row reconciliation.

```json
{
 "headline_cone": {
  "modules": 209,
  "module_rollups": {
   "OPEN": 155,
   "EQUALITY_PROVED": 5,
   "RECEIPTED": 40,
   "NO_ANNOTATED_DEFINITION_REACHED": 9
  },
  "definitions": {
   "OPEN": 915,
   "EQUALITY_PROVED": 435,
   "RECEIPTED": 258,
   "EQUALITY_DOMAIN": 4
  },
  "definitions_total": 1612,
  "open_wrong_basis_definitions": 247
 },
 "closed_roots_union": {
  "modules": 258,
  "module_rollups": {
   "OPEN": 169,
   "EQUALITY_PROVED": 9,
   "RECEIPTED": 70,
   "NO_ANNOTATED_DEFINITION_REACHED": 10
  },
  "definitions": {
   "OPEN": 953,
   "EQUALITY_PROVED": 450,
   "RECEIPTED": 374,
   "EQUALITY_DOMAIN": 4
  },
  "definitions_total": 1781
 },
 "rows": {
  "PROVENANCE_CLEAN_AT_DEFINITION_LEVEL": 114,
  "CONDITIONAL": 471,
  "UNASSESSED_ROOTLESS": 2,
  "NO_EMITTED_MODULE_REACHED": 12
 },
 "rows_relying_on_OPEN_module_module_level": 562,
 "splitB_open_breakdown": {
  "wrong_basis": 247,
  "failed_or_other": 81,
  "no_fresh_emission": 547,
  "no_record": 40
 }
}
```
