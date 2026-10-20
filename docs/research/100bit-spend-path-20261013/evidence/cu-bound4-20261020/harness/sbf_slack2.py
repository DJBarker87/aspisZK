#!/usr/bin/env python3
"""Second-method ELF audit of SBF register traces (PREREG-CU-UPPER-BOUND-2).

Reuses the first method's CFG / post-dominator / arm-path code
(`cu-bound-20261019/harness/sbf_slack.py`, imported unchanged) and changes:
  * traces are processed one at a time (bounded memory);
  * per trace and per executed conditional branch, the dynamic count and the
    taken count are kept (the per-site traced counts of method step 2);
  * per arm the longest and shortest instruction path to the immediate
    post-dominator is reported separately (fallthrough, target);
  * call nodes inside a region weigh 1 + the callee's inclusive cost, taken as
    the observed [min, max] over ALL traces given, or, for a callee never
    executed, its static acyclic longest/shortest inclusive path (recursive);
    a cyclic never-executed callee leaves the site 'call-unbounded';
  * per trace: instructions per function, syscall counts and length args.
usage: sbf_slack2.py --linked L --deployed D --trace label=path.regs ... --out out.json
"""
import argparse, collections, json, sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sbf_slack as S

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--linked', required=True); ap.add_argument('--deployed', required=True)
    ap.add_argument('--trace', action='append', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--abort-regex', default=r'panicking|panic_bounds_check|index_len_fail|index_order_fail|unwrap_failed|handle_alloc_error|raw_vec12handle_error|assert_failed|len_mismatch_fail|panic_already|expect_failed|panic_fmt|custom_panic|capacity_overflow|slice_start_index|slice_end_index|str_index_overflow|overflow_fail|5abort')
    a = ap.parse_args()
    linked = open(a.linked, 'rb').read(); deployed = open(a.deployed, 'rb').read()
    ls = S.elf_sections(linked); ds = S.elf_sections(deployed)
    lt = next(s for s in ls if s['name'] == '.text'); dt = next(s for s in ds if s['name'] == '.text')
    ltext = linked[lt['offset']:lt['offset'] + lt['size']]; dtext = deployed[dt['offset']:dt['offset'] + dt['size']]
    text_identical = ltext == dtext and lt['addr'] == dt['addr']
    assert text_identical
    T = S.Text(ltext, lt['addr']); RELOC = S.reloc_syscalls(deployed)
    funcs = [(v, sz, n) for v, sz, n in S.elf_functions(linked, ls) if lt['addr'] <= v < lt['addr'] + lt['size']]
    starts = [f[0] for f in funcs]
    import bisect
    def fn_of(slot):
        addr = T.base + 8 * slot; i = bisect.bisect_right(starts, addr) - 1
        if i >= 0 and addr < funcs[i][0] + funcs[i][1]: return i
        return None
    CALLCOST = {}; per_trace = []
    NEG = -10**12; POS = 10**12  # abort paths: never the longest, never the shortest
    for spec in a.trace:
        label, path = spec.split('=', 1)
        regs = S.read_regs(path); pcs = regs[11::12]
        counts = collections.Counter(); taken = collections.Counter()
        sys_calls = collections.defaultdict(collections.Counter); stack = []; prev = None; seq = {}; MOD = (1 << 61) - 1
        n = len(pcs)
        # minrem[b]: the fewest instructions any frame executed after its last execution of b
        # until it returned (inclusive of callees): the least remaining cost of the function at b.
        minrem = {}; frames_ = [{}]; callcount = collections.Counter(); callcount[pcs[0]] += 1
        for i in range(n):
            slot = pcs[i]
            counts[slot] += 1
            if prev is not None and T.kind(prev) == 'cond':
                bit = 1 if (slot == T.target(prev) and slot != prev + 1) else 0
                taken[prev] += bit
                seq[prev] = (seq.get(prev, 7) * 1000003 + 1 + bit) % MOD
            if T.kind(slot) == 'cond': frames_[-1][slot] = i
            op = T.op(slot)
            if op == 0x85 or op == 0x8d:
                name = RELOC.get(slot) if op == 0x85 else None
                if name and name.startswith('sol_'):
                    r = regs[12 * i:12 * i + 6]
                    sys_calls[name][int(r[3] if name.startswith('sol_mem') else r[2])] += 1
                elif i + 1 < n:
                    stack.append((pcs[i + 1], i)); frames_.append({}); callcount[pcs[i + 1]] += 1
            elif op == 0x95 and stack:
                entry, start = stack.pop(); c = i - start + 1
                lo, hi = CALLCOST.get(entry, (c, c)); CALLCOST[entry] = (min(lo, c), max(hi, c))
                for bb, ix in frames_.pop().items():
                    r_ = i - ix
                    if r_ < minrem.get(bb, 1 << 62): minrem[bb] = r_
            prev = slot
        for fr_ in frames_:
            for bb, ix in fr_.items():
                r_ = n - ix
                if r_ < minrem.get(bb, 1 << 62): minrem[bb] = r_
        per_fn = collections.Counter()
        for slot, c in counts.items():
            f = fn_of(slot); per_fn[f] += c
        conds = {s: (c, taken.get(s, 0)) for s, c in counts.items() if 0 <= s < T.n and T.kind(s) == 'cond'}
        per_trace.append(dict(label=label, total=n, conds=conds, per_fn=per_fn, seq=seq, counts_all=counts, taken_all=taken, minrem=minrem, callcount=callcount,
                              sys_calls={k: sorted(v.items()) for k, v in sys_calls.items()}))
        del regs, pcs
        print('trace', label, n, file=sys.stderr, flush=True)
    # Static inclusive cost of never-executed callees (acyclic call graph and CFG only).
    ABORT = re.compile(a.abort_regex)
    def is_abort(n, flags):
        """A call that never returns: a panic/abort routine or the sol_panic_/abort syscall.
        A path through it fails the transaction (out of scope)."""
        if n not in flags: return False
        if RELOC.get(n) in ('sol_panic_', 'abort'): return True
        tgt = T.call_target(n)
        if tgt is None: return False
        g = fn_of(tgt)
        return g is not None and bool(ABORT.search(funcs[g][2]))
    def u64(x): return x & ((1 << 64) - 1)
    def s64(x): x = u64(x); return x - (1 << 64) if x >> 63 else x
    def cond_decide(op, a, b):
        hi = op & 0xf0; ua, ub = u64(a), u64(b); sa, sb = s64(a), s64(b)
        return {0x10: ua == ub, 0x20: ua > ub, 0x30: ua >= ub, 0x40: (ua & ub) != 0, 0x50: ua != ub,
                0x60: sa > sb, 0x70: sa >= sb, 0xa0: ua < ub, 0xb0: ua <= ub, 0xc0: sa < sb, 0xd0: sa <= sb}[hi]
    CLONE = [0]
    def thread_constants(succ, flags, lo, hi):
        """Jump threading for materialised booleans: `mov rX, K` followed, through straight-line
        code that does not write rX, by `jCC rX, imm` is decided statically on that path. The
        straight-line nodes are cloned for this path (negative ids, weight 1), so other paths
        through them are unchanged. Removes CFG paths that no execution can take (e.g. an
        error arm falling into the success code through `jne r3, 0`)."""
        for m in [n for n in list(succ) if isinstance(n, int) and n >= 0]:
            op = T.op(m)
            if op not in (0xb7, 0xb4): continue
            r = T.text[8 * m + 1] & 0xf; K = T.imm(m) if op == 0xb7 else (T.imm(m) & 0xffffffff)
            chain = []; s = succ[m][0] if succ[m] else None; steps = 0
            while isinstance(s, int) and s >= 0 and steps < 16:
                k = T.kind(s); o = T.op(s)
                if k == 'cond':
                    if (T.text[8 * s + 1] & 0xf) == r and (o & 0x08) == 0:
                        taken = cond_decide(o, K, T.imm(s))
                        d = succ[s][1] if taken else succ[s][0]
                        prev = m
                        for c in chain:
                            CLONE[0] += 1; cid = -CLONE[0]; succ[prev] = [cid]; succ[cid] = []; prev = cid
                        succ[prev] = [d]
                    break
                if k in ('call', 'exit') or s in flags: break
                if k == 'ja':
                    chain.append(s); s = succ[s][0]; steps += 1; continue
                cls = o & 7
                if cls in (0, 1, 4, 7) and (T.text[8 * s + 1] & 0xf) == r: break  # writes rX
                chain.append(s); s = succ[s][0] if succ[s] else None; steps += 1
    cfg_cache = {}
    def cfg(f):
        """CFG of function f for ACCEPTED executions: a call to an abort routine is a dead end
        (no successor), so post-dominators are taken over paths that return normally."""
        if f not in cfg_cache:
            v, sz, name = funcs[f]; lo = (v - T.base) // 8; hi = lo + sz // 8
            succ, flags = S.build_cfg(T, lo, hi)
            for n in list(flags):
                if is_abort(n, flags): succ[n] = []
            # natural loops on the CFG as compiled (abort calls as dead ends), then jump threading
            # on the acyclic graph, so loop headers, bodies and entry counts refer to real slots
            succ2, loops, irreducible = cut_back_edges(succ, lo)
            thread_constants(succ2, flags, lo, hi)
            cfg_cache[f] = (succ2, flags, S.postdominators(succ2), lo)
            LOOPS[f] = dict(loops=loops, irreducible=irreducible, succ=succ2, flags=flags, succ_orig=succ)
        return cfg_cache[f]
    LOOPS = {}; BODIES = {}
    def cut_back_edges(succ, entry):
        """Natural loops: an edge u -> h is a back edge if h dominates u (forward dominators from
        the function entry). Each back edge is redirected to a virtual node ('B', h) whose only
        successor is the exit, so the graph is acyclic: a branch inside a loop body then has its
        join inside the iteration, and the loop itself becomes a trip-count site. A retreating
        edge to a non-dominator (irreducible loop) is reported."""
        order = []; seen = {entry}; st = [(entry, iter([s for s in succ.get(entry, []) if s != 'X']))]
        while st:
            n, it = st[-1]
            for s in it:
                if s not in seen and s in succ:
                    seen.add(s); st.append((s, iter([x for x in succ[s] if x != 'X']))); break
            else:
                st.pop(); order.append(n)
        rpo = list(reversed(order)); idx = {n: i for i, n in enumerate(rpo)}
        preds = collections.defaultdict(list)
        for n in rpo:
            for s in succ[n]:
                if s in idx: preds[s].append(n)
        idom = {entry: entry}; changed = True
        def inter(a, b):
            while a != b:
                while idx[a] > idx[b]: a = idom[a]
                while idx[b] > idx[a]: b = idom[b]
            return a
        while changed:
            changed = False
            for n in rpo[1:]:
                ps = [p for p in preds[n] if p in idom]
                if not ps: continue
                new = ps[0]
                for p in ps[1:]: new = inter(p, new)
                if idom.get(n) != new: idom[n] = new; changed = True
        def dominates(h, u):
            while True:
                if u == h: return True
                if u == entry or u not in idom: return False
                u = idom[u]
        succ2 = {n: list(v) for n, v in succ.items()}; loops = collections.defaultdict(list); irreducible = []
        for u in rpo:
            for k, s in enumerate(succ[u]):
                if s in idx and idx[s] <= idx[u]:
                    if dominates(s, u):
                        succ2[u][k] = ('B', s); succ2[('B', s)] = ['X']; loops[s].append(u)
                    else:
                        irreducible.append((u, s))
        bodies = {}
        for h, us in loops.items():
            body = {h}; st2 = [u for u in us if u != h]
            while st2:
                x = st2.pop()
                if x in body: continue
                body.add(x); st2.extend(p for p in preds[x] if p not in body)
            bodies[h] = body
        BODIES[id(succ2)] = bodies
        return succ2, dict(loops), irreducible
    def iter_longest(f, h):
        """Longest single iteration of loop h: path h -> ('B', h) over nodes that can reach it."""
        info = LOOPS[f]; succ, flags = info['succ'], info['flags']; target = ('B', h)
        memo = {}
        def walk(n):
            if n == target: return 0
            if n == 'X' or isinstance(n, tuple): return NEG
            if n in memo: return memo[n]
            memo[n] = NEG
            w, _ = call_weight(n, flags, True)
            r = max([walk(s) for s in succ[n]], default=NEG)
            memo[n] = (w + r) if r > NEG // 2 and w > NEG // 2 else NEG
            return memo[n]
        return walk(h)
    static_memo = {}
    def static_cost(entry, depth=0):
        """(longest, shortest) inclusive instruction count of a call to `entry`, or None if cyclic/unknown."""
        if entry in CALLCOST: return (CALLCOST[entry][1], CALLCOST[entry][0])
        if entry in static_memo: return static_memo[entry]
        static_memo[entry] = None
        f = fn_of(entry)
        if f is None or depth > 40: return None
        succ, flags, _, lo = cfg(f)
        if LOOPS[f]['loops'] or LOOPS[f]['irreducible']: return None  # a looping callee needs a cited cap
        memo = {}; onstack = set(); bad = [False]
        def w(n):
            if n in flags:
                if is_abort(n, flags): return (NEG, POS)
                tgt = T.call_target(n)
                if tgt is None: return (1, 1)
                c = static_cost(tgt, depth + 1)
                if c is None: bad[0] = True; return (1, 1)
                return (1 + c[0], 1 + c[1])
            return (1, 1)
        def walk(n):
            if n == 'X': return (0, 0)
            if n in memo: return memo[n]
            if is_abort(n, flags): return (NEG, POS)
            if n in onstack: raise ValueError('cycle')
            onstack.add(n); res = [walk(s) for s in succ[n]]; onstack.discard(n)
            hi, lo_ = w(n); r = (hi + max(x[0] for x in res), lo_ + min(x[1] for x in res)); memo[n] = r; return r
        try:
            r = walk(entry)
        except (ValueError, RecursionError, KeyError):
            return None
        if bad[0]: return None
        static_memo[entry] = (r[0] + 1, r[1] + 1)  # + exit accounting as in CALLCOST (call..exit inclusive)
        return static_memo[entry]
    fsys_memo = {}
    def fn_syscalls(entry):
        """Syscall names reachable from a call to `entry` (static call graph, transitive)."""
        f = fn_of(entry)
        if f is None: return set()
        if f in fsys_memo: return fsys_memo[f]
        fsys_memo[f] = set(); succ, flags, _, lo = cfg(f); names = set()
        for n in flags:
            if RELOC.get(n, '').startswith('sol_'): names.add(RELOC[n])
            tgt = T.call_target(n)
            if tgt is not None: names |= fn_syscalls(tgt)
        fsys_memo[f] = names; return names
    sys.setrecursionlimit(200000)
    branches = sorted({s for t in per_trace for s in t['conds']})
    import heapq
    def call_weight(n, flags, longest):
        """Weight of node n: 1, or 1 + callee inclusive cost; (value, unknown-callee-name or None)."""
        if isinstance(n, tuple): return 0, None  # virtual back-edge sink
        if n not in flags: return 1, None
        if is_abort(n, flags): return (NEG if longest else POS), None
        tgt = T.call_target(n)
        if tgt is None: return 1, None  # syscall: CU costed from the syscall schedule, not here
        c = static_cost(tgt)
        if c is None:
            g = fn_of(tgt); return 1, (funcs[g][2] if g is not None else hex(tgt))
        return 1 + (c[0] if longest else c[1]), None
    LMEMO = {}
    def arm_info(succ, flags, s0, join, fidx=None, enclosing=None):
        """Longest (None if the arm reaches a cycle before the join) and shortest path from s0 to join."""
        memo = LMEMO.setdefault((id(succ), join), {})  # node -> (longest, unknown callees) or 'cyc'
        onstack = set()
        def walk(n):
            if n == join or n == 'X': return (0, frozenset())
            m = memo.get(n)
            if m == 'cyc': raise ValueError('cycle')
            if m is not None: return m
            if n in onstack: raise ValueError('cycle')
            if is_abort(n, flags):
                memo[n] = (NEG, frozenset()); return memo[n]
            onstack.add(n)
            try:
                rs = [walk(s) for s in succ[n]]
            except ValueError:
                memo[n] = 'cyc'; raise
            finally:
                onstack.discard(n)
            w, u = call_weight(n, flags, True)
            unk = frozenset().union(*[r[1] for r in rs]) | (frozenset([u]) if u else frozenset())
            memo[n] = (w + max(r[0] for r in rs), unk); return memo[n]
        try:
            L, unknown = walk(s0)
        except ValueError:
            L, unknown = None, frozenset()
        # shortest path (Dijkstra on node weights, cycles allowed)
        dist = {}; pq = [(0, 0, s0)]; cnt = 1; S = None
        while pq:
            dd, _, n = heapq.heappop(pq)
            if n == join or n == 'X': S = dd; break
            if n in dist: continue
            dist[n] = dd; w, _u = call_weight(n, flags, False)
            if w >= POS: continue
            for s in succ[n]:
                if s not in dist: heapq.heappush(pq, (dd + w, cnt, s)); cnt += 1
        # reachable never-executed callees and syscalls before the join
        seen = set(); st = [s0]; ne = set(); names = set()
        while st:
            n = st.pop()
            if n == join or n in seen or n == 'X': continue
            seen.add(n); st.extend(succ[n])
            if n in flags:
                if RELOC.get(n, '').startswith('sol_'): names.add(RELOC[n])
                tgt = T.call_target(n)
                if tgt is not None:
                    names |= fn_syscalls(tgt)
                    if tgt not in CALLCOST:
                        g = fn_of(tgt); ne.add(funcs[g][2] if g is not None else hex(tgt))
        cyclic_unknown = sorted(unknown)
        continues = sorted(hex(T.base + 8 * n[1]) for n in seen if isinstance(n, tuple) and (enclosing is None or n[1] in enclosing))
        reached_loops = sorted(hex(T.base + 8 * n[1]) for n in seen if isinstance(n, tuple))
        L_exit = L_cont = None
        if continues:
            # Longest path that leaves through the function exit without continuing a loop, and
            # longest path that ends by continuing a loop (to a back-edge sink).
            def lw(mode):
                memo3 = {}
                def wk(n):
                    if isinstance(n, tuple):
                        enc = enclosing is None or n[1] in enclosing
                        return (0 if mode == 'cont' else NEG) if enc else (0 if mode == 'exit' else NEG)
                    if n == 'X' or n == join: return 0 if mode == 'exit' else NEG
                    if n in memo3: return memo3[n]
                    if is_abort(n, flags): memo3[n] = NEG; return NEG
                    memo3[n] = NEG
                    w, _ = call_weight(n, flags, True)
                    r = max([wk(s) for s in succ[n]], default=NEG)
                    memo3[n] = w + r if r > NEG // 2 else NEG; return memo3[n]
                v = wk(s0); return v if v > NEG // 2 else None
            L_exit, L_cont = lw('exit'), lw('cont')
        S_finish = None
        if continues:
            so = LOOPS[fidx]['succ_orig'] if fidx is not None else None
            if so is not None:
                dist2 = {}; pq2 = [(0, 0, s0[1] if isinstance(s0, tuple) else s0)]; c2 = 1
                while pq2:
                    dd, _, n = heapq.heappop(pq2)
                    if n == 'X': S_finish = dd; break
                    if n in dist2: continue
                    dist2[n] = dd; w, _u = call_weight(n, flags, False)
                    if w >= POS: continue
                    for s in so.get(n, []):
                        if s not in dist2: heapq.heappush(pq2, (dd + w, c2, s)); c2 += 1
        if L is not None and L < 0: L = 'abort'  # every path of this arm calls an abort routine before the join
        loops = None; L_dag = None
        if L is None:
            # Loops in the arm: strongly connected components of the arm's subgraph (abort calls are
            # dead ends). With N_i the trip cap of loop i, the arm costs at most
            # L_dag + sum_i (N_i - 1) * W_i, where L_dag is the longest path of the condensation with
            # each loop weighted once (W_i = sum of its node weights: one iteration at its longest).
            nodes = [n for n in seen]
            index = {}; low = {}; onst = set(); stack_ = []; comp = {}; ncomp = [0]; counter = [0]
            for root in nodes:
                if root in index: continue
                work = [(root, iter([s for s in succ[root] if s in seen]))]
                index[root] = low[root] = counter[0]; counter[0] += 1; stack_.append(root); onst.add(root)
                while work:
                    v, it = work[-1]
                    pushed = False
                    for wv in it:
                        if wv not in index:
                            index[wv] = low[wv] = counter[0]; counter[0] += 1; stack_.append(wv); onst.add(wv)
                            work.append((wv, iter([s for s in succ[wv] if s in seen]))); pushed = True; break
                        elif wv in onst:
                            low[v] = min(low[v], index[wv])
                    if pushed: continue
                    work.pop()
                    if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                    if low[v] == index[v]:
                        while True:
                            x = stack_.pop(); onst.discard(x); comp[x] = ncomp[0]
                            if x == v: break
                        ncomp[0] += 1
            members = collections.defaultdict(list)
            for n_, c_ in comp.items(): members[c_].append(n_)
            def wt(n_):
                w_, _ = call_weight(n_, flags, True); return max(w_, 0)
            cw_ = {c_: sum(wt(n_) for n_ in ms) for c_, ms in members.items()}
            cyc = {c_ for c_, ms in members.items() if len(ms) > 1 or ms[0] in succ[ms[0]]}
            memo2 = {}
            def walk2(c_):
                if c_ in memo2: return memo2[c_]
                outs = {comp[s] for n_ in members[c_] for s in succ[n_] if s in comp and comp[s] != c_}
                memo2[c_] = cw_[c_] + max([walk2(o) for o in outs], default=0); return memo2[c_]
            L_dag = walk2(comp[s0]) if s0 in comp else 0
            loops = [dict(header=hex(T.base + 8 * min(x for x in members[c_] if x >= 0)), W=cw_[c_], nodes=len(members[c_])) for c_ in sorted(cyc)]
        return dict(L=L, S=S, L_dag=L_dag, loops=loops, continues=continues, reached_loops=reached_loops, S_finish=S_finish, L_exit=L_exit, L_cont=L_cont, unbounded_callees=cyclic_unknown, never_executed_callees=sorted(ne), syscalls=sorted(names))
    rows = []
    for b in branches:
        f = fn_of(b)
        if f is None:
            rows.append(dict(slot=b, function='<unmapped>', cls='unmapped')); continue
        succ, flags, ipd, lo = cfg(f)
        join = ipd.get(b)
        row = dict(slot=b, addr=hex(T.base + 8 * b), function=funcs[f][2], fn_index=f, op=S.COND[T.op(b) & 0xf0],
                   backward=T.target(b) <= b, join=join)
        if join is None:
            row['cls'] = 'noexit'; rows.append(row); continue
        bodies = BODIES.get(id(succ), {})
        enclosing = {h for h, body in bodies.items() if b in body}
        row['enclosing_loops'] = sorted(hex(T.base + 8 * h) for h in enclosing)
        arms = [arm_info(succ, flags, s0, join, f, enclosing) for s0 in succ[b]]  # [fallthrough, target]
        conts = {int(c, 16) for a_ in arms for c in a_['continues']}
        conts = {(x - T.base) // 8 for x in conts}
        if conts:
            # innermost enclosing loop that an arm continues; exits and continues relative to it
            h0 = min(conts, key=lambda h: len(bodies[h]))
            row['loop'] = hex(T.base + 8 * h0)
            arms = [arm_info(succ, flags, s0, join, f, {h0}) for s0 in succ[b]]
        row['arms'] = arms
        cyc = [a['L'] is None for a in arms]
        row['abort_arms'] = [a['L'] == 'abort' for a in arms]
        row['cls'] = ('exit-' if join == 'X' else '') + ('acyclic' if not any(cyc) else ('both-cyclic' if all(cyc) else ('fallthrough-cyclic' if cyc[0] else 'target-cyclic')))
        if any(a['continues'] for a in arms): row['cls'] = 'loop-control'
        rows.append(row)
    # Loops of every executed function: single-iteration longest path and per-trace header
    # executions and back-edge traversals (entries = header executions - back traversals).
    loop_rows = []; ENTRY_MISMATCH = []
    for f, info in sorted(LOOPS.items()):
        for h, backs in sorted(info['loops'].items(), key=lambda kv: str(kv[0])):
            if not isinstance(h, int) or h < 0: continue
            W = iter_longest(f, h)
            # entries counted on the unmodified CFG: edge traversals into h from predecessors
            # outside the loop body (an edge p->h is traversed count(p) times for a straight-line
            # p, and taken(p) / count(p)-taken(p) times for a conditional p)
            v_, sz_, _n = funcs[f]; lo_ = (v_ - T.base) // 8; raw, _fl = S.build_cfg(T, lo_, lo_ + sz_ // 8)
            body = BODIES.get(id(info['succ']), {}).get(h, set())
            preds_h = [p_ for p_, ss in raw.items() if h in ss]
            per = []
            for t_ in per_trace:
                ch = t_['counts_all'].get(h, 0); ent = 0; bt = 0
                for p_ in preds_h:
                    cp = t_['counts_all'].get(p_, 0)
                    if T.kind(p_) == 'cond':
                        tk = t_['taken_all'].get(p_, 0); tgt_ = T.target(p_); nxt_ = p_ + 1
                        e_ = (tk if tgt_ == h else 0) + ((cp - tk) if nxt_ == h else 0)
                    else:
                        e_ = cp
                    if p_ in body: bt += e_
                    else: ent += e_
                if h == lo_: ent += t_['callcount'].get(h, 0)
                if ch != bt + ent: ENTRY_MISMATCH.append((funcs[f][2], hex(T.base + 8 * h), t_['label'], ch, bt, ent))
                per.append([ch, bt, max(ent, ch - bt)])  # never fewer entries than unexplained header executions
            loop_rows.append(dict(header=hex(T.base + 8 * h), function=funcs[f][2], W_iter=W if W > NEG // 2 else None,
                                  back_edges=[hex(T.base + 8 * u) for u in backs if isinstance(u, int) and u >= 0], per_trace=per))
    irr = {funcs[f][2]: len(i['irreducible']) for f, i in LOOPS.items() if i['irreducible']}
    # Second pass: the largest number of header executions within ONE entry of each loop
    # (frame-aware: the predecessor of a slot is the previous slot of the same frame; after a
    # call returns it is the call instruction).
    HB = {}
    for f, info in LOOPS.items():
        for h in info['loops']:
            if isinstance(h, int) and h >= 0:
                HB[h] = BODIES.get(id(info['succ']), {}).get(h, set())
    hdr_rows = {int(r['header'], 16) - T.base: r for r in loop_rows}
    hdr_rows = {(k // 8): v for k, v in hdr_rows.items()}
    for ti, spec in enumerate(a.trace):
        label, path = spec.split('=', 1)
        regs = S.read_regs(path); pcs = regs[11::12]; n = len(pcs)
        fprev = [None]; cur = [{}]; mx = collections.Counter()
        for i in range(n):
            s = pcs[i]
            if s in HB:
                pv = fprev[-1]; c = cur[-1]
                if pv is None or pv not in HB[s]: c[s] = 1
                else: c[s] = c.get(s, 0) + 1
                if c[s] > mx[s]: mx[s] = c[s]
            op = T.op(s)
            if op == 0x85 or op == 0x8d:
                name = RELOC.get(s) if op == 0x85 else None
                if not (name and name.startswith('sol_')) and i + 1 < n:
                    fprev[-1] = s; fprev.append(None); cur.append({}); continue
            elif op == 0x95 and len(fprev) > 1:
                fprev.pop(); cur.pop(); continue
            fprev[-1] = s
        for h, r in hdr_rows.items():
            r.setdefault('max_trip_per_entry', []).append(mx.get(h, 0))
        del regs, pcs
    out = dict(text_identical_linked_vs_deployed=text_identical, text_addr=hex(T.base), text_slots=T.n,
               functions=[f[2] for f in funcs], branches=rows,
               traces=[dict(label=t['label'], instructions=t['total'],
                            counts=[t['conds'].get(r['slot'], (0, 0))[0] for r in rows],
                            taken=[t['conds'].get(r['slot'], (0, 0))[1] for r in rows],
                            seq=[t['seq'].get(r['slot'], 0) for r in rows],
                            minrem=[t['minrem'].get(r['slot']) for r in rows],
                            per_fn={str(k): v for k, v in t['per_fn'].items()}, syscalls=t['sys_calls']) for t in per_trace],
               inclusive_call_costs={str(fn_of(e)): list(v) for e, v in CALLCOST.items() if fn_of(e) is not None},
               loops=loop_rows, irreducible_functions=irr, loop_entry_mismatches=ENTRY_MISMATCH[:200], loop_entry_mismatch_count=len(ENTRY_MISMATCH))
    json.dump(out, open(a.out, 'w'))
    print(json.dumps(dict(branches=len(rows), traces=len(per_trace), classes=collections.Counter(r['cls'] for r in rows))))

if __name__ == '__main__':
    main()
