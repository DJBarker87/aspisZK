#!/usr/bin/env python3
"""Apply the site rules to sbf_slack.py output (one program/transaction role).

Rules (REPORT.md section 3):
 R1 both arms observed and the full per-site decision sequence differs between
    traces (different witness/masks/position/split) -> data-dependent value
    site: extra = (longest - shortest) path to the post-dominator x max count.
 R0 both arms observed but the decision sequence is identical in every trace
    of the kind (positional pattern, e.g. Vec growth, unrolled index tests):
    not data-dependent within the traced kind; extra 0 (empirical, listed).
 R2 one arm never observed, and its longest path <= the observed arm's
    shortest path -> measured arm already the costliest: extra 0.
 R3 one arm never observed but possibly longer -> conservative site:
    extra = (unobserved longest - observed shortest) x max count.
 R4 region calls a never-executed callee that is a panic/abort/alloc-failure
    routine on the unobserved arm -> that arm aborts the transaction
    (rejected, out of scope): extra 0. Other never-executed callees -> UNMAPPED.
 R5 loop-class branches: reported with per-trace counts; data-dependent trip
    counts are identified by count variation among traces of equal split and
    capped from source (sites.json).
Every instruction is 1 CU; syscall charges are costed separately.
"""
import json, re, sys, collections
PANIC = re.compile(r'panicking|panic_bounds_check|slice_(end|start)_index_len_fail|slice_index_order_fail|'
                   r'unwrap_failed|handle_alloc_error|raw_vec12handle_error|assert_failed|len_mismatch_fail|'
                   r'panic_already|expect_failed|panic_fmt|custom_panic|abort')
d = json.load(open(sys.argv[1])); split_of = json.loads(sys.argv[2]) if len(sys.argv) > 2 else None
labels = [t['label'] for t in d['traces']]
tot = collections.Counter(); rows = []; unmapped = []; loops = []
for b in d['branches']:
    mx = max(b['counts']); cls = b['cls']
    seen_t = any(x > 0 for x in b['taken']); seen_f = any(x < c for x, c in zip(b['taken'], b['counts']))
    rule = None; extra = 0
    if cls in ('diamond', 'call-bounded'):
        (fl, fs), (tl, ts) = b['arms_fallthrough_target']
        if seen_t and seen_f and not b.get('sequence_varies', True):
            rule = 'R0'
        elif seen_t and seen_f:
            rule = 'R1'; extra = (max(fl, tl) - min(fs, ts)) * mx
        else:
            obs_s, un_l = (ts, fl) if seen_t else (fs, tl)
            if un_l <= obs_s: rule = 'R2'
            else: rule = 'R3'; extra = (un_l - obs_s) * mx
    elif cls == 'call-unobserved':
        if all(PANIC.search(u) for u in b['unobserved_callees']): rule = 'R4'
        else: rule = 'UNMAPPED'; unmapped.append(b)
    elif cls == 'loop':
        rule = 'R5'; loops.append(b)
    else:
        rule = 'UNMAPPED'; unmapped.append(b)
    tot[rule] += extra; tot[rule + '#'] += 1
    if extra: rows.append(dict(addr=b['addr'], function=b['function'], rule=rule, extra=extra, max_count=mx,
                               per_exec=extra // mx, both=b['both_directions_observed']))
rows.sort(key=lambda r: -r['extra'])
byfn = collections.Counter()
for r in rows: byfn[r['function']] += r['extra']
# Loop sites whose execution count varies among traces of the same split value.
var_loops = []
for b in loops:
    groups = collections.defaultdict(set)
    for lab, c in zip(labels, b['counts']):
        groups[split_of.get(lab) if split_of else 0].add(c)
    if any(len(v) > 1 for v in groups.values()):
        var_loops.append(dict(addr=b['addr'], function=b['function'], counts=b['counts'], taken=b['taken']))
fns = d['functions']; total = max(t['instructions'] for t in d['traces'])
out = dict(totals=dict(tot), top_sites=rows[:60], extra_by_function=byfn.most_common(),
           unmapped=[dict(addr=b['addr'], function=b['function'], cls=b['cls'], callees=b.get('unobserved_callees'),
                          counts=b['counts'], taken=b['taken']) for b in unmapped],
           data_dependent_loops=var_loops, traces=d['traces'], syscalls=d['syscalls'])
json.dump(out, open(sys.argv[3] if len(sys.argv) > 3 else '/dev/stdout', 'w'), indent=1)
print(json.dumps(dict(tot)), 'unmapped', len(unmapped), 'varying loops', len(var_loops), file=sys.stderr)
