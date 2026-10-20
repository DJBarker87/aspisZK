#!/usr/bin/env python3
"""Per-function ELF control-flow audit of SBF register traces.

Inputs: the linked (unstripped) SBF ELF, the deployed (stripped) ELF it was
stripped into, and one or more LiteSVM register traces (`*.regs`, 12 u64 per
executed instruction, pc in r11) of that program.

For every conditional branch executed in any trace it reports the executing
function, dynamic count, taken counts per trace, and a static "slack": the
difference between the longest and the shortest instruction path from the
branch to its immediate post-dominator inside the function, provided that
region is acyclic and call-free (diamond/triangle). Branches whose region
contains a loop, a call or a function exit are classified separately.

Method-step mapping (PREREG-CU-UPPER-BOUND): slack x max dynamic count is the
"analytical maximum extra cost over the cheapest path x maximum execution
count" of an ELF value-branch site. Loop sites are reported with per-trace
trip totals so data-dependent trip counts can be identified and capped from
source. Every instruction costs 1 CU (Agave); syscalls add their own charges,
which this tool does not model (they are costed from source in sites.json).
"""
import argparse, collections, json, struct, sys

def u16(b, o): return struct.unpack_from('<H', b, o)[0]
def u32(b, o): return struct.unpack_from('<I', b, o)[0]
def u64(b, o): return struct.unpack_from('<Q', b, o)[0]

def elf_sections(data):
    assert data[:4] == b'\x7fELF' and data[4] == 2 and data[5] == 1
    shoff = u64(data, 0x28); shentsize = u16(data, 0x3a); shnum = u16(data, 0x3c); shstrndx = u16(data, 0x3e)
    secs = []
    for i in range(shnum):
        o = shoff + i * shentsize
        secs.append(dict(name_off=u32(data, o), type=u32(data, o + 4), addr=u64(data, o + 0x10),
                         offset=u64(data, o + 0x18), size=u64(data, o + 0x20), link=u32(data, o + 0x28),
                         entsize=u64(data, o + 0x38)))
    strtab = secs[shstrndx]
    for s in secs:
        n = data[strtab['offset'] + s['name_off']:]
        s['name'] = n[:n.index(b'\0')].decode()
    return secs

def elf_functions(data, secs):
    out = []
    for s in secs:
        if s['type'] != 2:  # SHT_SYMTAB
            continue
        st = secs[s['link']]
        for o in range(s['offset'], s['offset'] + s['size'], 24):
            name_off = u32(data, o); info = data[o + 4]; value = u64(data, o + 8); size = u64(data, o + 16)
            if info & 0xf == 2 and size:  # STT_FUNC
                n = data[st['offset'] + name_off:]
                out.append((value, size, n[:n.index(b'\0')].decode('utf-8', 'replace')))
    return sorted(set(out))

COND = {0x10: 'jeq', 0x20: 'jgt', 0x30: 'jge', 0x40: 'jset', 0x50: 'jne', 0x60: 'jsgt', 0x70: 'jsge',
        0xa0: 'jlt', 0xb0: 'jle', 0xc0: 'jslt', 0xd0: 'jsle'}

class Text:
    def __init__(self, text, base):
        self.text = text; self.base = base; self.n = len(text) // 8
    def op(self, pc): return self.text[8 * pc]
    def off(self, pc): return struct.unpack_from('<h', self.text, 8 * pc + 2)[0]
    def imm(self, pc): return struct.unpack_from('<i', self.text, 8 * pc + 4)[0]
    def kind(self, pc):
        op = self.op(pc)
        if op == 0x18: return 'lddw'
        if op & 7 == 5:
            hi = op & 0xf0
            if hi == 0x00: return 'ja'
            if hi == 0x80: return 'call'
            if hi == 0x90: return 'exit'
            if hi in COND: return 'cond'
        return 'alu'
    def width(self, pc): return 2 if self.op(pc) == 0x18 else 1
    def target(self, pc): return pc + 1 + self.off(pc)
    def call_target(self, pc):
        """Internal bpf-to-bpf call (src=1): pc-relative imm; None for syscalls/callx."""
        if self.op(pc) == 0x85 and (self.text[8 * pc + 1] >> 4) == 1:
            return pc + 1 + self.imm(pc)
        return None

def build_cfg(T, lo, hi):
    """Successor lists for slots in [lo, hi). 'X' = leaves function (exit/outside jump)."""
    succ = {}; flags = {}
    pc = lo
    while pc < hi:
        k = T.kind(pc); w = T.width(pc)
        nxt = pc + w
        s = []
        if k == 'exit':
            s = ['X']
        elif k == 'ja':
            t = T.target(pc); s = [t if lo <= t < hi else 'X']
        elif k == 'cond':
            t = T.target(pc)
            s = [nxt if nxt < hi else 'X', t if lo <= t < hi else 'X']
        else:
            s = [nxt if nxt < hi else 'X']
        if k == 'call':
            flags[pc] = 'call'
        succ[pc] = s
        pc = nxt
    return succ, flags

def postdominators(succ):
    """Immediate post-dominator per node via Cooper-Harvey-Kennedy on the reverse CFG."""
    nodes = list(succ.keys()) + ['X']
    pred_rev = collections.defaultdict(list)  # reverse graph successors = original predecessors
    for a, ss in succ.items():
        for b in ss:
            pred_rev[b].append(a)
    # reverse-graph DFS from X gives order; reverse-graph preds = original succs
    order = []; seen = set(['X']); stack = [('X', iter(pred_rev['X']))]
    while stack:
        node, it = stack[-1]
        for child in it:
            if child not in seen:
                seen.add(child); stack.append((child, iter(pred_rev[child]))); break
        else:
            stack.pop(); order.append(node)
    rpo = list(reversed(order)); index = {n: i for i, n in enumerate(rpo)}
    ipdom = {'X': 'X'}
    def intersect(a, b):
        while a != b:
            while index[a] > index[b]: a = ipdom[a]
            while index[b] > index[a]: b = ipdom[b]
        return a
    changed = True
    while changed:
        changed = False
        for n in rpo[1:]:
            cands = [s for s in succ[n] if s in ipdom]
            if not cands: continue
            new = cands[0]
            for s in cands[1:]: new = intersect(s, new)
            if ipdom.get(n) != new:
                ipdom[n] = new; changed = True
    return ipdom  # nodes unreachable to X (infinite loops) are absent

ARMS = {}

def region_paths_weighted(T, succ, flags, b, join, callcost):
    """Like region_paths, but call nodes weigh 1 + [min,max] observed inclusive callee cost.
    Returns ('call-bounded', longest, shortest) or ('call-unobserved', callee-list) or a loop/exit class."""
    region = set(); stack = list(succ[b])
    while stack:
        n = stack.pop()
        if n == join or n in region: continue
        if n == 'X': return ('exit', None, None)
        region.add(n); stack.extend(succ[n])
    unobserved = []
    for n in region:
        if n in flags:
            tgt = T.call_target(n)
            if tgt is not None and tgt not in callcost: unobserved.append(tgt)
    if unobserved: return ('call-unobserved', None, None, unobserved)
    memo = {}; onstack = set()
    def w(n):
        if n in flags:
            tgt = T.call_target(n)
            if tgt is None: return (1, 1)  # syscall: instruction only; syscall CU costed separately
            lo, hi = callcost[tgt]; return (1 + hi, 1 + lo)
        return (1, 1)
    def walk(n):
        if n == join: return (0, 0)
        if n in memo: return memo[n]
        if n in onstack: raise ValueError('cycle')
        onstack.add(n)
        res = [walk(s) for s in succ[n]]
        onstack.discard(n)
        hi, lo = w(n)
        r = (hi + max(x[0] for x in res), lo + min(x[1] for x in res)); memo[n] = r; return r
    try:
        res = [walk(s) for s in succ[b]]
    except ValueError:
        return ('loop', None, None)
    ARMS[b] = res
    return ('call-bounded', max(x[0] for x in res), min(x[1] for x in res))

def region_paths(T, succ, flags, b, join):
    """Longest/shortest instruction count from b (inclusive) to join (exclusive)
    over the region; None classification if cyclic/call/exit inside."""
    region = set(); stack = [s for s in succ[b]]
    while stack:
        n = stack.pop()
        if n == join or n in region: continue
        if n == 'X': return ('exit', None, None)
        region.add(n); stack.extend(succ[n])
    if any(n in flags for n in region): return ('call', None, None)
    # cycle check + longest/shortest via DFS memo
    memo = {}; onstack = set()
    def walk(n):
        if n == join: return (0, 0)
        if n in memo: return memo[n]
        if n in onstack: raise ValueError('cycle')
        onstack.add(n)
        res = [walk(s) for s in succ[n]]
        onstack.discard(n)
        r = (1 + max(x[0] for x in res), 1 + min(x[1] for x in res))
        memo[n] = r; return r
    try:
        sys.setrecursionlimit(100000)
        res = [walk(s) for s in succ[b]]
    except ValueError:
        return ('loop', None, None)
    ARMS[b] = res
    return ('diamond', max(x[0] for x in res), min(x[1] for x in res))

def reloc_syscalls(data):
    """slot -> imported symbol name for R_BPF_64_32 relocations against .dynsym
    (syscalls are resolved by the loader; their call imm in the file is a placeholder)."""
    secs = elf_sections(data)
    dyn = next(s for s in secs if s['name'] == '.dynsym'); ds = secs[dyn['link']]
    tx = next(s for s in secs if s['name'] == '.text'); out = {}
    for s in secs:
        if s['type'] != 9: continue
        for o in range(s['offset'], s['offset'] + s['size'], 16):
            off, info = struct.unpack_from('<QQ', data, o); sym = info >> 32
            if sym and info & 0xffffffff == 10:
                no = u32(data, dyn['offset'] + 24 * sym); n = data[ds['offset'] + no:]
                out[(off - tx['addr']) // 8] = n[:n.index(b'\0')].decode()
    return out

def read_regs(path):
    data = open(path, 'rb').read()
    return memoryview(data).cast('Q')

def murmur3_32(data, seed=0):
    c1, c2 = 0xcc9e2d51, 0x1b873593; h = seed; n = len(data)
    for i in range(0, n - n % 4, 4):
        k = int.from_bytes(data[i:i + 4], 'little')
        k = (k * c1) & 0xffffffff; k = ((k << 15) | (k >> 17)) & 0xffffffff; k = (k * c2) & 0xffffffff
        h ^= k; h = ((h << 13) | (h >> 19)) & 0xffffffff; h = (h * 5 + 0xe6546b64) & 0xffffffff
    tail = data[n - n % 4:]; k = 0
    for i, b in enumerate(tail): k |= b << (8 * i)
    if tail:
        k = (k * c1) & 0xffffffff; k = ((k << 15) | (k >> 17)) & 0xffffffff; k = (k * c2) & 0xffffffff; h ^= k
    h ^= n; h ^= h >> 16; h = (h * 0x85ebca6b) & 0xffffffff; h ^= h >> 13; h = (h * 0xc2b2ae35) & 0xffffffff; h ^= h >> 16
    return h

SYSCALLS = ['sol_panic_', 'sol_log_', 'sol_log_64_', 'sol_log_pubkey', 'sol_log_compute_units_',
            'sol_create_program_address', 'sol_try_find_program_address', 'sol_sha256', 'sol_keccak256',
            'sol_get_clock_sysvar', 'sol_get_rent_sysvar', 'sol_memcpy_', 'sol_memmove_', 'sol_memset_',
            'sol_memcmp_', 'sol_get_stack_height', 'sol_set_return_data', 'sol_get_return_data',
            'sol_invoke_signed_c', 'sol_invoke_signed_rust', 'sol_log_data', 'sol_alloc_free_',
            'sol_get_processed_sibling_instruction', 'sol_remaining_compute_units']
SYSCALL_BY_HASH = {murmur3_32(n.encode()): n for n in SYSCALLS}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--linked', required=True); ap.add_argument('--deployed', required=True)
    ap.add_argument('--trace', action='append', required=True, help='label=path.regs')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    linked = open(a.linked, 'rb').read(); deployed = open(a.deployed, 'rb').read()
    ls = elf_sections(linked); ds = elf_sections(deployed)
    lt = next(s for s in ls if s['name'] == '.text'); dt = next(s for s in ds if s['name'] == '.text')
    ltext = linked[lt['offset']:lt['offset'] + lt['size']]; dtext = deployed[dt['offset']:dt['offset'] + dt['size']]
    text_identical = ltext == dtext and lt['addr'] == dt['addr']
    T = Text(ltext, lt['addr'])
    RELOC = reloc_syscalls(deployed)
    funcs = [(v, sz, n) for v, sz, n in elf_functions(linked, ls) if lt['addr'] <= v < lt['addr'] + lt['size']]
    # sbpf pc -> slot index in .text. Detect the offset: entrypoint text_addr? use first trace pc histogram.
    traces = []
    for spec in a.trace:
        label, path = spec.split('=', 1)
        regs = read_regs(path)
        traces.append((label, regs[11::12], regs))
    # Map pc to text slot: sbpf v0 pc counts slots from start of .text when text vaddr is the program start.
    # Determine the shift by requiring every traced pc to land on a decodable instruction start.
    def fn_of(slot):
        addr = T.base + 8 * slot
        lo, hi = 0, len(funcs) - 1
        while lo <= hi:
            mid = (lo + hi) // 2; v, sz, n = funcs[mid]
            if addr < v: hi = mid - 1
            elif addr >= v + sz: lo = mid + 1
            else: return mid
        return None
    shift = 0
    CALLCOST = {}
    per_trace = []
    for label, pcs, regs in traces:
        counts = collections.Counter(); taken = collections.Counter(); per_fn = collections.Counter()
        sys_calls = collections.defaultdict(list)
        stack = []; prev = None; seq = {}
        for i, pc in enumerate(pcs):
            slot = pc - shift
            counts[slot] += 1
            if prev is not None and T.kind(prev) == 'cond':
                bit = 1 if slot == T.target(prev) else 0
                taken[prev] += bit
                seq[prev] = (seq.get(prev, 7) * 1000003 + 1 + bit) % ((1 << 61) - 1)
            op = T.op(slot)
            if op == 0x85 or op == 0x8d:
                if not (op == 0x85 and RELOC.get(slot, '').startswith('sol_')) and i + 1 < len(pcs):
                    stack.append((pcs[i + 1] - shift, i))
            elif op == 0x95 and stack:
                entry, start = stack.pop(); c = i - start + 1
                lo, hi = CALLCOST.get(entry, (c, c)); CALLCOST[entry] = (min(lo, c), max(hi, c))
            if T.op(slot) == 0x85:
                name = RELOC.get(slot)
                if name and name.startswith('sol_'):
                    r = regs[12 * i:12 * i + 6]
                    f = fn_of(slot)
                    sys_calls[name].append(dict(slot=slot, caller=funcs[f][2] if f is not None else None,
                                                r1=r[1], r2=r[2], r3=r[3]))
            prev = slot
        for slot, c in counts.items():
            f = fn_of(slot); per_fn[funcs[f][2] if f is not None else '<unmapped>'] += c
        per_trace.append(dict(label=label, total=len(pcs), counts=counts, taken=taken, per_fn=per_fn, sys_calls=sys_calls, seq=seq))
    # Union of executed conditional branches.
    branches = sorted({s for t in per_trace for s, c in t['counts'].items() if 0 <= s < T.n and T.kind(s) == 'cond'})
    cfg_cache = {}
    rows = []
    for b in branches:
        f = fn_of(b)
        if f is None:
            rows.append(dict(slot=b, function='<unmapped>', cls='unmapped')); continue
        v, sz, name = funcs[f]
        lo = (v - T.base) // 8; hi = lo + sz // 8
        if f not in cfg_cache:
            succ, flags = build_cfg(T, lo, hi); cfg_cache[f] = (succ, flags, postdominators(succ))
        succ, flags, ipd = cfg_cache[f]
        backward = T.target(b) <= b
        join = ipd.get(b)
        cls, longest, shortest = ('noexit', None, None) if join is None else region_paths(T, succ, flags, b, join)
        unobserved = None
        if cls == 'call':
            r = region_paths_weighted(T, succ, flags, b, join, CALLCOST)
            cls = r[0]
            if cls == 'call-bounded': longest, shortest = r[1], r[2]
            elif cls == 'call-unobserved':
                unobserved = sorted({funcs[fn_of(x)][2] if fn_of(x) is not None else hex(x) for x in r[3]})
        counts = [t['counts'].get(b, 0) for t in per_trace]
        tk = [t['taken'].get(b, 0) for t in per_trace]
        both = any(0 < x < c for x, c in zip(tk, counts)) or (any(x > 0 for x in tk) and any(x < c for x, c in zip(tk, counts)))
        rows.append(dict(slot=b, addr=hex(T.base + 8 * b), function=name, op=COND[T.op(b) & 0xf0],
                         backward=backward, cls=cls, longest=longest, shortest=shortest,
                         slack=(longest - shortest) if cls in ('diamond', 'call-bounded') else None,
                         unobserved_callees=unobserved,
                         arms_fallthrough_target=[list(x) for x in ARMS[b]] if b in ARMS and cls in ('diamond', 'call-bounded') else None,
                         join=join if isinstance(join, int) else None,
                         counts=counts, taken=tk, both_directions_observed=both,
                         count_varies=len(set(counts)) > 1, taken_varies=len(set(tk)) > 1,
                         sequence_varies=len({t['seq'].get(b) for t in per_trace if t['counts'].get(b)}) > 1))
    fn_totals = collections.defaultdict(list)
    for t in per_trace:
        for n, c in t['per_fn'].items(): fn_totals[n].append(c)
    out = dict(text_identical_linked_vs_deployed=text_identical, text_addr=hex(T.base), text_slots=T.n,
               traces=[dict(label=t['label'], instructions=t['total']) for t in per_trace],
               functions={n: dict(per_trace=[t['per_fn'].get(n, 0) for t in per_trace]) for n in fn_totals},
               syscalls=[{name: dict(count=len(v),
                                     len_arg_values=sorted(collections.Counter((x['r3'] if name.startswith('sol_mem') else x['r2']) for x in v).items()),
                                     callers=sorted(collections.Counter(x['caller'] for x in v).items(), key=lambda kv: -kv[1])[:20])
                          for name, v in t['sys_calls'].items()} for t in per_trace],
               inclusive_call_costs={(funcs[fn_of(e)][2] if fn_of(e) is not None else hex(e)): list(v) for e, v in CALLCOST.items()},
               branches=rows)
    json.dump(out, open(a.out, 'w'), indent=1)
    print(json.dumps(dict(text_identical=text_identical, branches=len(rows), traces=[(t['label'], t['total']) for t in per_trace])))

if __name__ == '__main__':
    main()
