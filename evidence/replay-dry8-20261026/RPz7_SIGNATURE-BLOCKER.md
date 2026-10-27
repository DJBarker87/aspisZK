# Historical cached signature unavailable

RPz7_1480 exits1,wall0.7066146819852293s,peak1522628KiB,
swaps0;one6G/8G/Swap0/Tasks64 scope,Lean-j1-M7000.

The historical Rc10_Top.olean itself matches its pinned4a8fd228… hash and
218680-byte size (RPz7_BeforeKernel-preflight.json). Its exact recorded
LEAN_PATH fails to resolve a transitive member of the cached import closure:

```text
RPz7_sources/RPz7_BeforeKernel.lean:1:0: error: object file '/home/dombarker/project-offloads/codex-cx-import-union-20261022/objects/AspisR1CircleSampleWrapper/Funs.olean' of module AspisR1CircleSampleWrapper.Funs does not exist
```

No alternate object,producer,source,library root or kernel statement is
substituted. No host/launcher repair is attempted. This inspection chain is
stopped and its unchanged input is not retried. Independent fresh-context
audits use RPz7_overlay,including the already rebuilt circle source module;
they do not depend on this missing historical cache path.

Both complete SOURCE statements are retained identically. No historical
before KERNEL signature was recovered,and no fresh after top exists. The
required full kernel byte-identity test therefore remains UNESTABLISHED.
Transport leakage into that statement is neither asserted nor disproved.
There is no RPz7_STATEMENT-FINDING:the semantic-leak gate was not reached.
