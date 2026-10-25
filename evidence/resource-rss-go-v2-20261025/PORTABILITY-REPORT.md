Source-only portability continuation on codex/cx-resource-rss-go-v2-20261025,
base 468619b15180119560c138c83127da58ba3b4c23. Design committed first at
8d12e9b395; implementation/focused tests committed at 367e786cd8.

Established locally: retained Linux AS/DATA [-1,-1] pass the new explicit remote
Linux validator on Darwin without changing any live rlimit. The immutable old
checker still raises exactly `unexpected inherited restriction: RLIMIT_AS`.
This repairs a representation mismatch, not a finite host restriction or a
resource failure. No deployed-target result follows.

Before: `inspect()` called `host.check_limits(info['inherited_limits'])`, whose
AS/DATA condition is `[resource.RLIM_INFINITY, resource.RLIM_INFINITY]` from the
LOCAL runtime. After: `inspect()` calls `check_remote_linux_limits(info)`, which
requires exact metadata `{platform: 'linux', rlim_infinity: -1}`, exact integer
pairs (excluding bool), supported values, and AS/DATA exactly [-1,-1]. The
bootstrap checks Linux/-1 before inventory, checks its local limits, and reports
metadata; local stage validates saved metadata before packaging. Numeric maps
are unmodified. Optional expected-map comparison is full equality. Existing
host preflight/run/final comparisons remain byte-identical and same-platform.
All other local call sites were inspected; no further host-sentinel application
was found. Historical preparation/failure audit programs remain source-specific,
not runnable new-source attestations.

Full exact before/after source, unified diff and per-function AST statements
are PORTABILITY-local-{before,after}.py.txt, PORTABILITY-source.diff and
PORTABILITY-AST-diff.json. Only inspection_payload, check_remote_linux_limits,
inspect and stage differ; other top-level AST is identical. Eleven of twelve
mapped modules and every historical evidence file are byte-identical. No
shipped/model/policy/security/trust source or assumptions changed.

New validation commands (all prefixed `python3 -B
tools/resource-rss-go-v2-20261025/ResourceRssGOv2_receipt.py`):

- `ResourceRssGOv2_PORTABILITY_tests.py PORTABILITY-focused`: exit0,
  wall0.4851930411532521s, peak37044224B, swap0; six groups.
- After adding exact generated-platform-predicate cases (the reason for the
  second run), `ResourceRssGOv2_PORTABILITY_tests.py PORTABILITY-predicate-focused`:
  exit0, wall0.46730824979022145s, peak37437440B, swap0; six groups.
- `ResourceRssGOv2_PORTABILITY_seal.py PORTABILITY-seal-audit`: exit0,
  wall1.111223875079304s, peak103251968B, swap0; source audit, no test replay.

Receipts retain expanded exact argv, source revision, interpreter/source pins;
PORTABILITY-seal.json retains dependency hashes, old/new module hashes, current
source/dirtystate, immutable evidence pins and future argv explicitly marked
UNAUTHORIZED. Axioms=N/A throughout (no Lean/theorem execution).

Tests cover finite AS/DATA either side, unsupported negatives, malformed pairs,
bools/types, missing fields, bad platform/infinity, every map-cell mismatch,
unlimited-cell mismatch and missing/extra keys in expected maps. Exact bootstrap
executes with job imports forbidden and ONLY runtime inventory stubbed; Darwin
rejects before inventory/capture. Its exact platform predicate/metadata expression
are separately evaluated on controlled values, not by faking live platform or
resource limits. Actual new local.inspect executes against stubbed SSH, retained
capture plus controlled-source metadata, and fresh TEMP writes; verifies charge
before transport, one call, no retry after success/failure, no downstream actions.
No retained remote runtime payload was re-executed. No old suite replay.

Mapping justification: local Darwin SDK source explicitly defines (1<<63)-1;
retained pin-attested Linux Python capture supplies -1. The new bootstrap enforces
this fixed Linux wire contract rather than accepting a caller-chosen sentinel.
No fresh Linux documentation/inventory/download or host validation is claimed.

Zero SSH/network/host/stage/preflight/run/export/GO/marker/native/Lean/compiler/ELF
operations. Epoch USED1/1 and all FIVE earlier failed metadata epochs stay
charged. Kani59/60 final RESERVED; both deployed targets not established.
Next concrete deliverable: independent lead review of this minimal delta and
boundary evidence, followed only under a separate allocation by a copy/preparation
driver that explicitly accounts for the delta. Old identity mapping and seals
were not rewritten. No merge or push.
