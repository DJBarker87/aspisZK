#!/usr/bin/env python3
"""X7: the SBF compiler's "Stack offset of N exceeded max offset of 4096" messages of two builds of each program
(reference = the frozen tree, candidate), compared per function. The symbol is the legacy Rust mangling; it is
demangled here (length-prefixed path segments, `$LT$`-style escapes decoded, the trailing `17h<hash>E` dropped), so the
same function in two builds compares equal although its hash differs. Per function: the largest stack offset in each
build; status same / new / gone / larger / smaller. Reached: whether a function with the same crate, the same last
path segment and the same module segments (impl segments ignored) is in the candidate emission's LLBC of that program
(Charon's LLBC holds what the host build reaches from the entry; an approximation by name, stated as such). Reads only.
usage: fv_emit_stack.py <reference sbf dir> <candidate sbf dir> <candidate run dir>   (TSV on stdout; summary last)"""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x1b_llbc import LLBC

ESC = {'$LT$': '<', '$GT$': '>', '$C$': ',', '$u20$': ' ', '$RF$': '&', '$BP$': '*', '$u7b$': '{', '$u7d$': '}', '$u5b$': '[',
       '$u5d$': ']', '$u3b$': ';', '$u27$': "'", '$u2b$': '+', '$LP$': '(', '$RP$': ')', '..': '::', '$SP$': '@', '$u21$': '!'}


def demangle(sym):
    m = re.match(r'_ZN(.*)E$', sym)
    if not m:
        return sym
    s, out, i = m.group(1), [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j].isdigit():
            j += 1
        if j == i:
            break
        n = int(s[i:j])
        seg = s[j:j + n]
        i = j + n
        if re.fullmatch(r'h[0-9a-f]{16}', seg):
            continue
        if seg.startswith('_$'):
            seg = seg[1:]
        for k, v in ESC.items():
            seg = seg.replace(k, v)
        out.append(seg)
    return '::'.join(out)


def load(d):
    res = {}
    p = Path(d) / 'stack.txt'
    if not p.exists():
        return None
    for l in p.read_text(errors='replace').splitlines():
        m = re.search(r'Function (\S+) Stack offset of (\d+)', l)
        if m:
            f = demangle(m.group(1))
            res[f] = max(res.get(f, 0), int(m.group(2)))
    return res


ref, cand, run = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
print('program\tfunction\treference offset\tcandidate offset\tstatus\treached (by name, candidate LLBC)')
summary = []
for P in ('verifier', 'pool'):
    a, b = load(ref / P), load(cand / P)
    if a is None or b is None:
        summary.append('%s: missing stack list (%s)' % (P, 'reference' if a is None else 'candidate'))
        continue
    ll = run / P / 'charon' / 'out.llbc'
    names = []
    if ll.exists():
        g = LLBC(str(ll))
        names = [n.split('::') for n in g.name.values()]

    def reached(f):
        segs = [x for x in re.sub(r'<[^<>]*>', '', f).split('::') if x and not x.startswith('{')]
        if not segs:
            return 'n/a'
        for n in names:
            q = [x for x in n if not x.startswith('{')]
            if q and q[0] == segs[0] and q[-1] == segs[-1] and all(x in n for x in segs[1:-1] if x[:1].islower()):
                return 'yes: ' + '::'.join(n)
        return 'no'
    cnt = {}
    for f in sorted(set(a) | set(b)):
        x, y = a.get(f), b.get(f)
        st = 'new' if x is None else 'gone' if y is None else 'same' if x == y else 'larger' if y > x else 'smaller'
        cnt[st] = cnt.get(st, 0) + 1
        print('%s\t%s\t%s\t%s\t%s\t%s' % (P, f, x if x is not None else '-', y if y is not None else '-', st, reached(f)))
    summary.append('%s: reference %d functions, candidate %d; %s' % (P, len(a), len(b), ', '.join('%s %d' % kv for kv in sorted(cnt.items()))))
for s in summary:
    print('# ' + s)
