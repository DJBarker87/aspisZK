#!/usr/bin/env python3
"""Aspis extraction probe: assign each Lean error of a compile log to the declaration of the emitted file it falls in.
usage: XP_errmap.py <flat Funs .lean> <lean stdout.log> [json-out]"""
import re, sys, json, collections
src = open(sys.argv[1]).read().split('\n'); log = open(sys.argv[2], errors='replace').read()
# declaration starts: a doc comment `/-- [` at column 0 opens a block that runs to the next one
starts = [i for i, l in enumerate(src) if l.startswith('/-- ')]
def block(line):  # 1-based line -> (rust name, lean name, start line)
    import bisect
    k = bisect.bisect_right(starts, line - 1) - 1
    if k < 0: return ('<header>', '<header>', 0)
    s = starts[k]; e = starts[k + 1] if k + 1 < len(starts) else len(src)
    rust = re.sub(r'^/-- (Trait implementation: |Trait declaration: )?', '', src[s]).strip()
    lean = None
    for j in range(s, e):
        m = re.match(r'^(?:@\[.*\]\s*)?(?:noncomputable\s+)?(?:def|structure|inductive|abbrev|axiom|instance|theorem)\s*(\S*)', src[j])
        if m:
            lean = m.group(1) or src[j + 1].strip().split()[0]; break
    return (rust, lean, s + 1)
errs = collections.OrderedDict()
for m in re.finditer(r'(?m)^[^\n:]*\.lean:(\d+):(\d+): error(?:\([^)]*\))?: ([^\n]*(?:\n(?![^\n:]*\.lean:\d+:\d+: )[^\n]*){0,6})', log):
    line = int(m.group(1)); rust, lean, s = block(line)
    errs.setdefault(lean, dict(rust=rust, lean=lean, start=s, errors=[]))['errors'].append(dict(line=line, text=' '.join(m.group(3).split())[:400]))
out = list(errs.values())
decls = []
for k, s in enumerate(starts):
    r, l, _ = block(s + 1); decls.append(l)
print('declarations %d, with errors %d, error lines %d' % (len(decls), len(out), sum(len(x['errors']) for x in out)))
for x in out:
    print('- %s  [%s]' % (x['lean'], x['rust'][:150]))
    for e in x['errors'][:3]: print('     %d: %s' % (e['line'], e['text'][:260]))
if len(sys.argv) > 3: json.dump(dict(declarations=decls, failing=out), open(sys.argv[3], 'w'), indent=1)
