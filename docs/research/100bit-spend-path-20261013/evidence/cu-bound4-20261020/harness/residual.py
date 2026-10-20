#!/usr/bin/env python3
"""Per-site residuals and B per variant (PREREG-CU-UPPER-BOUND-2 steps 2-5).

usage: residual.py <analysis dir> <runs.json> <rules.json> <out dir>
<analysis dir>/{stage1,stage2,pool}.json: sbf_slack2.py over the traced runs (CFG with abort
calls as dead ends, constant jump threading, natural-loop back edges cut to per-loop sinks).
runs.json: per traced run {kind, split, mode, prefund, pairs, stage1_cu, settlement_cu, ...}.

For a variant V (stage 1: kind, split; settlement: kind, split, history mode, prefund) and its
measured worst run w, CU(x) - CU(w) for any accepted run x of V is bounded by the sum of:
 * branch sites (join inside an iteration or the function): own(b) =
     taken_w*(Lmax - L_t) + (count_w - taken_w)*(Lmax - L_f), L_arm the longest path of the arm
     to the join (nested regions at their longest, calls at the callee's maximum inclusive
     cost), Lmax over the arms that can execute in V. Nested regions lie inside the arms, so
     the sum over sites does not omit any instruction. An arm not observed in a traced run of V
     can execute (is counted) unless every path of it calls an abort routine (the transaction
     fails) or rules.json gives a code-cited exclusion.
 * loop-control sites (an arm continues a loop): the in-iteration choice as above over the
   continuing paths; an early exit at most once per loop entry: entries_w * (L_exit -
   S_finish), minrem the fewest instructions any frame of w executed after b before returning (traced);
 * loops: a loop whose header and back-edge counts are identical in all traced runs of V and
   which no unobserved arm can lengthen is positional (L0, residual 0); otherwise it needs a
   cited trip cap N (per entry): (N * entries_w - header_count_w) * W_iter, W_iter the longest
   single iteration (inner loops once; their own trips are their own sites).
R0: both arms taken but the decision sequence identical in all traced runs of V (>= 3 runs):
positional, residual 0 (the first method's R0).
"""
import json, sys, collections, re
A, RUNS, RULES, OUT = sys.argv[1:5]
runs = json.load(open(RUNS)); rules = json.load(open(RULES))
MIN_R0_TRACES = 3
ABORT = re.compile(rules['abort_callee_regex'])
LINES = {}
def frames(role, addr):
    if role not in LINES:
        LINES[role] = json.load(open(f'{A}/lines-{role}.json'))
        try: LINES[role].update(json.load(open(f'{A}/hdrlines-{role}.json')))
        except FileNotFoundError: pass
    return ' | '.join(f[0] + ' ' + f[1] for f in ((LINES[role].get(addr) or {}).get('frames') or []))
def group_of(role, meta):
    if role == 'stage1': return (meta['kind'], meta['split'])
    return (meta['kind'], meta['split'], meta['mode'], meta['prefund'])
def env(V): return dict(kind=V[0], split=V[1], mode=V[2] if len(V) > 2 else None, prefund=V[3] if len(V) > 3 else None)
def frame_list(role, addr):
    frames(role, addr)
    return (LINES[role].get(addr) or {}).get('frames') or []
def match(r, role, fn, addr, V):
    if 'inner_regex' in r or 'ws_regex' in r:
        fr = frame_list(role, addr)
        inner = fr[0][1] if fr else ''
        ws = next((f[1] for f in fr if 'rust/library' not in f[1] and '.cargo' not in f[1]), '')
        if 'inner_regex' in r and not re.search(r['inner_regex'], inner): return False
        if 'ws_regex' in r and not re.search(r['ws_regex'], ws): return False
    if r['role'] not in (role, '*'): return False
    if 'addr' in r and addr not in (r['addr'] if isinstance(r['addr'], list) else [r['addr']]): return False
    if 'function_regex' in r and not re.search(r['function_regex'], fn): return False
    if 'src_regex' in r and not re.search(r['src_regex'], frames(role, addr)): return False
    if 'applies' in r and not eval(r['applies'], {}, env(V)): return False
    return True
def exclusion(role, b, arm, V):
    a = b['arms'][0 if arm == 'f' else 1]
    callees = ' '.join(a.get('never_executed_callees', []) + a.get('unbounded_callees', []))
    for r in rules['exclusions']:
        if not match(r, role, b['function'], b['addr'], V) or r.get('arm', arm) != arm: continue
        if 'arm_callee_regex' in r and not re.search(r['arm_callee_regex'], callees): continue
        return r['id']
    return None
def callee_extra(role, arm, notes, missing):
    extra = 0
    for c in arm['unbounded_callees']:
        if ABORT.search(c): continue
        r = next((r for r in rules['callee_caps'] if r['role'] in (role, '*') and re.search(r['callee_regex'], c)), None)
        if r is None: missing.append(c)
        else: extra += r['cost']; notes.append('callee-cap:' + r['id'])
    return extra

result = {}; sites_out = []; unclassified = []; loop_out = []
for role in ['stage1', 'stage2', 'pool']:
    d = json.load(open(f'{A}/{role}.json'))
    labels = [t['label'] for t in d['traces']]; meta = {l: runs[l] for l in labels}
    groups = collections.defaultdict(list)
    for i, l in enumerate(labels): groups[group_of(role, meta[l])].append(i)
    br = d['branches']; key = 'stage1_cu' if role == 'stage1' else 'settlement_cu'
    loops_by_hdr = {l['header']: l for l in d['loops']}
    for V, idxs in sorted(groups.items()):
        wi = max(idxs, key=lambda i: meta[labels[i]][key]); w = d['traces'][wi]
        tot = collections.Counter(); per_site = []; must_cap = set()
        exits_possible = collections.defaultdict(list); exits_observed = collections.defaultdict(list); arm_loops = collections.defaultdict(int)
        entries_w = {h: l['per_trace'][wi][2] for h, l in loops_by_hdr.items()}
        for k, b in enumerate(br):
            if 'arms' not in b: continue
            cw, tw = w['counts'][k], w['taken'][k]
            obs = set(); obs_all = set()
            for i, t in enumerate(d['traces']):
                c, tk = t['counts'][k], t['taken'][k]
                s = ({'t'} if tk > 0 else set()) | ({'f'} if c - tk > 0 else set())
                obs_all |= s
                if i in idxs: obs |= s
            if not obs: continue
            arms = {'f': b['arms'][0], 't': b['arms'][1]}; n_w = {'t': tw, 'f': cw - tw}
            row = dict(addr=b['addr'], function=b['function'], cls=b['cls'], count_w=cw, taken_w=tw, observed_in_V=sorted(obs),
                       arms_longest=[arms['f']['L'], arms['t']['L']], arms_shortest=[arms['f']['S'], arms['t']['S']])
            notes = []; own = 0; missing = []
            possible = set(obs)
            for u in 'ft':
                if u in obs: continue
                if arms[u]['L'] == 'abort': notes.append(f'{u}:abort'); continue
                rid = exclusion(role, b, u, V)
                if rid: notes.append(f'{u}:excluded:{rid}'); continue
                possible.add(u); notes.append(f'{u}:counted:' + ('other-variant' if u in obs_all else 'never-taken'))
            # looping never-executed callees matter only on counted unobserved arms: inside an
            # observed arm they lie on sub-paths decided by nested sites
            extra = {a: (callee_extra(role, arms[a], notes, missing) if a not in obs else 0) for a in possible}
            # loops entered only through a counted unobserved arm (not enclosing b, not entered
            # by an observed arm as well): each such entry may run to the loop's trip cap
            seen_obs = {h for a in obs for h in arms[a]['reached_loops']} | set(b.get('enclosing_loops') or [])
            for u in possible - obs:
                for h in arms[u]['reached_loops']:
                    if h not in seen_obs: arm_loops[h] += max(cw, 1)
            if b['cls'] == 'loop-control':
                h0 = b['loop']
                # in-iteration choice between paths that continue the innermost loop
                Lc = {a: arms[a]['L_cont'] + extra[a] for a in possible if arms[a]['L_cont'] is not None}
                seqs = {d['traces'][i]['seq'][k] for i in idxs if d['traces'][i]['counts'][k]}
                positional = obs == {'f', 't'} and possible == obs and len(seqs) == 1 and len(idxs) >= MIN_R0_TRACES
                if positional: notes.append('positional-choice(R0)')
                if Lc and not positional:
                    Lcmax = max(Lc.values())
                    for a in obs:
                        if arms[a]['L_cont'] is not None: own += n_w[a] * max(0, Lcmax - arms[a]['L_cont'])
                for a in possible:
                    # pure exits only: an arm that can still continue the loop decides its exits deeper
                    if arms[a]['L_exit'] is not None and not arms[a]['continues']:
                        exits_possible[h0].append(arms[a]['L_exit'] + extra[a])
                        if a in obs: exits_observed[h0].append(arms[a]['L_exit'])
                    if a not in obs and arms[a]['continues']: must_cap.add(h0)
                rule = 'LC'
            else:
                if any(not isinstance(arms[a]['L'], int) for a in possible):
                    unclassified.append(dict(role=role, V=V, addr=b['addr'], function=b['function'], why='arm without a path bound (irreducible)'))
                    rule = 'R?'
                else:
                    Lmax = max(arms[a]['L'] + extra[a] for a in possible)
                    own = sum(n_w[a] * (Lmax - arms[a]['L']) for a in 'ft' if n_w[a])
                    row['L_max'] = Lmax
                    seqs = {d['traces'][i]['seq'][k] for i in idxs if d['traces'][i]['counts'][k]}
                    if obs == {'f', 't'}:
                        if len(seqs) == 1 and len(idxs) >= MIN_R0_TRACES and possible == obs:
                            rule = 'R0'; own = 0
                        else: rule = 'R1'
                    else:
                        rule = 'R2' if own == 0 else 'R3'
                    # syscalls reachable only on a counted unobserved arm: their CU is not an
                    # instruction count; charge each at its cap once per execution of b
                    obs_sys = {s for a in obs for s in arms[a]['syscalls']}
                    syscalls = sorted({s for a in possible - obs for s in arms[a]['syscalls']} - obs_sys)
                    if own and syscalls:
                        row['counted_arm_syscalls'] = syscalls
                        sy = 0
                        for s in syscalls:
                            c = rules['syscall_caps'].get(s)
                            if c is None:
                                unclassified.append(dict(role=role, V=V, addr=b['addr'], function=b['function'], why='syscall on a counted arm without a cost cap', syscall=s))
                            else: sy += c
                        row['syscall_surcharge'] = cw * sy; own += cw * sy
            if missing:
                unclassified.append(dict(role=role, V=V, addr=b['addr'], function=b['function'], why='counted arm calls a looping never-executed callee', callees=missing))
            row.update(rule=rule, residual=own, notes=notes)
            tot[rule] += own; tot[rule + '#'] += 1
            per_site.append(row)
        # loops inside counted unobserved arms but never executed in V: need caps
        for h, nexec in arm_loops.items():
            l = loops_by_hdr.get(h)
            if True:  # a new entry of the loop through an unobserved arm: its further iterations need a cap
                r = next((r for r in rules['loop_caps'] if match(r, role, l['function'] if l else '', h, V)), None)
                if r is None:
                    unclassified.append(dict(role=role, V=V, addr=h, function=l['function'] if l else '?', why='loop inside a counted unobserved arm, no cap'))
                else:
                    n = (max((l or {}).get('max_trip_per_entry') or [0]) if r['N'] == 'observed'
                         else (eval(str(r['N']), {}, env(V)) if isinstance(r['N'], str) else r['N']))
                    Wi = (l or {}).get('W_iter') or r.get('W_iter')
                    if Wi is None:
                        unclassified.append(dict(role=role, V=V, addr=h, function='?', why='loop inside a counted unobserved arm, no iteration bound'))
                    else:
                        res = nexec * max(0, n - 1) * Wi
                        tot['LA'] += res; tot['LA#'] += 1
                        per_site.append(dict(addr=h, function=l['function'] if l else '?', cls='loop-in-arm', rule='LA', cap=r['id'], N=n, residual=res))
        # loops
        for h, l in loops_by_hdr.items():
            per = [l['per_trace'][i] for i in idxs]
            if not any(x[0] for x in per): continue

            const = len({tuple(x) for x in per}) == 1 and len(idxs) >= MIN_R0_TRACES
            cw_h, bw_h, ew = l['per_trace'][wi]
            lrow = dict(header=h, function=l['function'], W_iter=l['W_iter'], header_count_w=cw_h, entries_w=ew,
                        counts_in_V=sorted({tuple(x) for x in per}))
            if const and h not in must_cap:
                lrow.update(rule='L0', residual=0)
                cited = next((r for r in rules['loop_caps'] if match(r, role, l['function'], h, V)), None)
                if cited:
                    lrow['source_cap_id'] = cited['id']
                    lrow['source_cap_citation'] = cited['citation']
            else:
                r = next((r for r in rules['loop_caps'] if match(r, role, l['function'], h, V)), None)
                if r is None or l['W_iter'] is None:
                    unclassified.append(dict(role=role, V=V, addr=h, function=l['function'], why='loop trip count varies or can be lengthened, no cap',
                                             counts=lrow['counts_in_V'][:4], forced=h in must_cap))
                    lrow.update(rule='L?', residual=0)
                else:
                    if r['N'] == 'observed':
                        # trip count fixed by compile-time constants: its maximum per entry is
                        # reached in every run, so the traced maximum is the maximum
                        n = max(l.get('max_trip_per_entry') or [0])
                    else:
                        n = eval(str(r['N']), {}, env(V)) if isinstance(r['N'], str) else r['N']
                    res = max(0, n * ew - cw_h) * l['W_iter']
                    lrow.update(rule='L1', cap=r['id'], N=n, residual=res)
            # an early or different exit at most once per entry: longest possible exit tail minus
            # the shortest observed one (tails are longest paths; their deficits in w are other sites)
            if exits_possible.get(h):
                lo_obs = min(exits_observed[h]) if exits_observed.get(h) else 0
                ex = max(0, ew) * max(0, max(exits_possible[h]) - lo_obs)
                lrow['exit_residual'] = ex; lrow['residual'] += ex
            tot[lrow['rule']] += lrow['residual']; tot[lrow['rule'] + '#'] += 1
            per_site.append(dict(lrow, addr=h, cls='loop'))
            loop_out.append(dict(lrow, role=role, V=V))
        nz = sorted([s for s in per_site if s['residual']], key=lambda s: -s['residual'])
        result.setdefault(role, {})[json.dumps(V)] = dict(worst=labels[wi], worst_cu=meta[labels[wi]][key], traces=[labels[i] for i in idxs],
                                                         totals=dict(tot), residual_sum=sum(s['residual'] for s in per_site),
                                                         syscall_flags=[s for s in per_site if s.get('counted_arm_syscalls')], top=nz[:40])
        sites_out.append(dict(role=role, variant=V, worst=labels[wi], sites=per_site))
json.dump(dict(result=result, unclassified=unclassified), open(f'{OUT}/residuals.json', 'w'), indent=1)
json.dump(sites_out, open(f'{OUT}/sites-per-variant.json', 'w'))
for role, vs in result.items():
    for V, r in vs.items():
        print(role, V, r['worst'], r['worst_cu'], 'residual', r['residual_sum'], {k: v for k, v in r['totals'].items() if not k.endswith('#') and v})
print('unclassified', len(unclassified), collections.Counter((u['role'], u['why']) for u in unclassified))
