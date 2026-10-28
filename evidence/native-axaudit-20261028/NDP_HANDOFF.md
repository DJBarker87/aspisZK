# Handoff: strict import-wide axiom inventory

Branch: `codex/cx-native-axaudit-20261028`. No push. Prefix NDP_.

**No reachable nonstandard axiom.** Both raw kernel dependency walks and both
`#print axioms` results contain exactly `propext`, `Classical.choice`, and
`Quot.sound`. The requested strict enumeration and classification are complete
for the two separately pinned compiled import forests. This supplies the audit
evidence for L188 missing obligation 3; it does not adopt unused axioms.

- Headline: 12,712 modules, 115,256 reachable constants, 108 imported axioms.
- Joint: 15,068 modules, 885,779 reachable constants, 108 imported axioms.
- Union: 18,982 modules, 115 axiom names, 147 distinct module/name/type
  declarations. Classification: 3 standard, 144 unreachable, 0 reachable
  nonstandard. Each root separately has 105 unreachable nonstandard axioms.
- Important finding: 32 shared axiom names have different types in the two
  forests. All variants are preserved. Fourteen other names occur in only one
  forest. Do not merge declarations by name alone or claim a shared environment.
- All eight FunsExternal module variants were inspected; each has zero axioms
  in its imported compiled declaration table. Aeneas/library/core/generated
  axioms elsewhere were all inventoried, including sorryAx and compiler axioms.

Read `NDP_AXIOMS.json` for every declaration, exact type expression, forest
membership, reachability and evidence. `NDP_AXIOM_AUDIT.md` explains the method,
trust boundaries, variant example and all execution results.
`NDP_ATTEMPTS.jsonl` retains admissions, compiles and corrections. Per-attempt
source snapshots, receipts and stdout are retained. Exhaustive visited-name
sets are compressed with uncompressed SHA256 files. `NDP_validate.py --check`
checks the evidence without running Lean.

Six Lean compiles out of twenty were used. NDP_R005 passed under normal caps
(exit 0, 17.432785 s, 6,335,160 KiB peak RSS, swaps 0). NDP_R006 failed during
joint import at -M7000, before the audit. NDP_R007 used its one delegated,
hash-verified lead agg16 exception and passed (exit 0, 36.363324 s, 8,870,164 KiB,
swaps 0). All scopes had TasksMax 64 and swap 0. The earlier own-input launcher
race and log-namespace typo are recorded and corrected; no failed result is
used as final evidence.

Reused: predecessor compiled objects, with 67,241 copied artifacts independently
verified (30,302,068,760 bytes). The original cache was read-only; own cache
`/home/dombarker/project-offloads/codex-cx-axaudit-cache-20261028` is retained.
No existing proved module, implementation, artifact or theorem hypothesis
changed; no assumption was discharged or added. This is not a fresh coherent
closure rebuild.

**Overall release target not yet established.** Next: the lead integrates this
packet into obligation 3 while retaining the other four L188 blockers: coherent
shared replay, D188/native-extraction/S10 completeness, joint installed-world/
producer reconciliation, and runtime/ELF execution association. Named theorem
hypotheses and runtime/native trust boundaries retain their L188 scope.
