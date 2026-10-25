# Private-name transport investigation — SOURCE ONLY, not validated

Pinned Lean 4.32 Environment.lean SHA256
100b207523d1005ae87f62f4e1693806854a35c59cd9b3210dfeeaa875d0ff98.
Exact source/API pins retained in preflight/attempt359. No Lean/toolchain edits.

## Public API findings

Kernel.Environment.addDeclCore (294+) normally checks a Declaration and uses
exact Names. Environment.addDeclCore (701–732) checks first, then registers both
private/public async metadata through AsyncConsts.add. That function (459–468)
indexes privateToUserName into a single-entry trie and panics for normalized
collisions. The thirteen original pairs remain in reused-result358.json.

Official Replay.lean state uses Kernel.Environment and default addDeclCore,
returning ofKernelEnv. That avoids elaborator async registration for replay,
but is not an established bridge into a later ordinary elaborator environment.
ofKernelEnv (645+) explicitly warns its result is temporary, not for leakage
into elaboration. find?/findConstVal?/findTask (820–843) inspect base.constants.map1,
then async metadata; they do not search arbitrary checked-task/map2 constants.
SMap.switch (96+) only flips stage1=false. Public mkEmptyEnvironment (1503+)
already switches to stage2, so rebuilding in an empty environment does not
supply a map1 workaround. updateBaseAfterKernelAdd (2420+) is private and chiefly
handles old-codegen metadata. replayConsts (2489+) reuses AsyncConsts.add;
its derivation precondition and async list source also prevent using it as an
arbitrary checked-kernel promotion API. finalizeImport constructs imported maps
but raw importing untrusted project CIs would bypass the required normal check.
No such import was executed.

No supported public API that meets all required transport guards was found.
No kernel coexistence/lookup test actually ran:359 failed at parsing the names.
PrivateName.lean29 supplies mkPrivateNameCore: it constructs a numeric zero
segment. The uncompiled corrected diagnostic uses that public function instead
of the invalid backtick `.0` syntax. No retry or test result is implied.

## Concrete representation-only proposal for lead/toolchain review

This must remain SOURCE ONLY. It requires a reviewed API inside the owning Lean
module; the private kernel constructor forbids an external implementation. It
is not a recommendation to rewrite records or trust-import DATA in this job.

Proposed API shape (pseudocode; deliberately not executable):

```
adoptNormallyCheckedExactConstants(baseElab, checkedKernel, checkedReceipt)
  require checkedReceipt covers EVERY added declaration/group by addDeclCore
  require baseElab's old constants are strict-identical in checkedKernel
  require header/trust/quotInit/extensions agree with checked provenance
  before := enumerate BOTH checkedKernel.constants.map1 and map2
  reject ANY duplicate exact Name (even if logically/propositionally equal)
  imported := fold before into fresh exact-Name hashmap; no normalization
  promoted := owning-module representation-only move to map1, empty map2
  require before.keyset == promoted.keyset, cardinalities identical
  require strict-v3 EVERY ConstantInfo before/after (type/value/metadata/rules)
  require strict full ctor/recursor/group guards and accepted axiom walk
  construct elaborator base+checked coherently using owning-module API
  require env.find?/findConstVal? resolve EVERY original exact Name
  require identical base/checked keysets and strict EVERY CI, no extras
  preserve module-origin and visibility records; no invented source identity
  reconstruct namespace/notation/extensions separately with checked provenance
```

No new logical declaration enters during promotion. Any changed CI requires a
new normal kernel check. A coherent visibility/extension/module-origin policy
and review of the ofKernelEnv warning are essential unresolved design details;
copying map2 to map1 by a private record rewrite is NOT an authorized shortcut.
Only after that review could a bounded synthetic test and actual exact-name
context transport establish this interface. No PANIC suppression, old-name
renaming, first-wins or comparator weakening is proposed.
