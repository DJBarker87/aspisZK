#!/usr/bin/env python3
"""Write the proposed disjoint ownership partition; does not launch workers."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ledger=json.loads((ROOT/'design/PRIVACY-FN-LEDGER-20261108.json').read_text())
packages={x:[] for x in ['W1','W2','W3','W4','W5','W6','C-thread','C-slice']}
for row in ledger['rows']:
 p,i=row['path'],row['emitted_id']
 if p=='thread':
  if row['kind']=='LEAF': job='W1'
  elif i in [124,126,216,218,222,315]: job='W2'
  elif i in [166,270,361,443,458,537]: job='W3'
  elif i in [0,1,6,'F0->f361@14756']: job='C-thread'
  else: job='W4'
 else:
  if i==0: job='C-slice'
  elif row['kind']=='LEAF' or i in [31,32,33,35,47,48,59]: job='W5'
  else: job='W6'
 packages[job].append(row['id'])
assert sum(map(len,packages.values()))==len(ledger['rows'])
assert len({i for v in packages.values() for i in v})==len(ledger['rows'])
(ROOT/'evidence/pv-ledger-20261108/job-partition.json').write_text(json.dumps(packages,indent=2)+'\n')
text="""# Stream B function jobs — B-y / LOG D860

This is a proposal, not a launch. Six disjoint work packages and two root
composition jobs own every ledger row exactly once. Counts below include
LEAF rows; no package owns another package's proof files. The exact row sets
are also in `evidence/pv-ledger-20261108/job-partition.json`.

Finish **OwnInit on the thread path first**. Start W1, then W2 as soon as its
leaves are available; W3 and W4 consume W1/W2 contracts. C-thread composes
continuously and is the first root completion gate. Queue W5/W6 and C-slice
until OwnInit is CLOSED; do not spread the proof effort onto the slice root
before that gate. The six packages describe available ownership, not six
mandatory simultaneous jobs. At most six workers under B-y; respect each
worker's single capped scope and the aggregate reservation barrier.

## Packages and acceptance

| Job | Responsibility | Immediate order / reused evidence |
| --- | --- | --- |
| W1 | Thread LEAF boundary and documented-semantics inventory | First 217, 312, 313, 320, 134, 344, BoxNew, then 121/123 counters, 214 clone, 318 higher-order catch, TLS/next93 and other named children. Audit exact argument/reply/modified footprints. Reuse installed thread-4/6/7/13/15 facts; no fixed-success children. Intrinsic318's callback is f316, never erased by arbitrary reply. |
| W2 | Arc/Packet construction and access: 124, 126, 216, 218, 222, 315 | Leaves -> 315/218 and 216, then 124; 320 -> 222 -> 126. Reuse complete local124/126 runs and Packet local returns with explicit final stores. Prove one full call-entry/return/frame theorem per function; derive entry root for126 from actual124 Post. |
| W3 | Spawn/ThreadInit box subtree: 166, 270, 361, 443, 458, 537 | Leaves -> 537 -> 458; 134/344 -> 443; then 361, 270, 166. Consume W2 at actual12801/13323. Reuse f361/Packet segments and source-derived casts14119/14121; preserve vtable115 and exact caller-cell deltas. f361's Post records the OwnInit milestone plus every return/terminal branch, not merely arrival at14756. |
| W4 | TLS/catch/callback/loop subtree: 2, 5, 17, 170, 125, 219, 316, 220, 208, 15, 164 | Leaves -> 170/17 -> 2/5; 164 and W3 -> 15 -> 208 -> 220 -> 316 -> 219 -> 125. Reuse original-entry syntax/certificates as fragments only. Derive source captures from entry Pre; retain Some/None iteration split, all failures and pending. No F0 theorem relabelled as a local contract. |
| W5 | Slice LEAF and allocation subtree: 31, 32, 33, 35, 47, 48, 59 | After OwnInit: leaf facts/frames -> 59 -> 47/48 -> 35 -> 31; close UB-check functions32/33 under pinned config. Reuse f31/f35 local returns and allocation branch results, with zero-size/error/null branches and complete frame. |
| W6 | Slice clone and sixteen-column loop subtree | After OwnInit and W5: finish21 from source262 through copy/set_len/return, then13, 6/8 and wrappers; close9 by one iteration plus sixteen-iteration induction, then4/2/1. Reuse QUniformReturn/QColumnViewReturn Post fragments. Arbitrary caller suffix and actual pointer/length/OWNER/world; no renaming/choice/alias premise. |

## Root composition

**C-thread** owns f0, f1, f6 and the OwnInit composition target. It consumes
W1–W4 contracts at actual arguments, derives OrderedFamiliesEntryOwned' and
intermediate representations from the original entry, applies the actual box
ownership/registration clauses, and closes OwnInit first. Reuse the current
whole-run evidence and later tagged-q5 transport without treating either as
a per-function closure. The closure conclusion covers the spawning Some
case, None exit, fault/abort/divergence and pending at the actual request.
A complete-return row is not closed just because its prefix reaches the box.
Caller obligations for captures/world/resource failure independence remain
explicit; no extra endpoint premise or T field is introduced.

**C-slice** owns slice f0 / Programs.source7. After W5/W6 are CLOSED, instantiate
the actual sixteen-column loop contracts and preserve the original entry-owned
witnesses/registry. Close the complete source7 return and its frame. Foundation
construction must discharge Source7EntryOwned''' at the caller; parent linkage,
erasure, fuel/projections and release correspondence remain separately named
obligations unless this composition actually proves them.

A job reports checker totals and the exact row ids newly CLOSED. Acceptance
requires one own-call-entry theorem, arbitrary full replies then actual CLOSED
callee instantiation, complete return/terminal/pending cases, explicit final
store/frame, verbatim printed hypothesis inventory, and complete exact-root
raw audit with standard axioms only. Preserve evidence and report remaining
hypotheses; no progress measured by theorem counts or trace length.

## Exact disjoint ownership

"""
for job,ids in packages.items():
 text+=f'### {job} ({len(ids)} rows)\n\n'+', '.join('`'+i+'`' for i in ids)+'.\n\n'
(ROOT/'design/PRIVACY-FN-JOBS-20261108.md').write_text(text)
for k,v in packages.items():print(k,len(v))
