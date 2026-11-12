#!/usr/bin/env python3
"""X2: completeness per crate (the lead's addition). For the Pool crate and each Aspis library crate in the LLBC, every
function declaration with a body that TP_llbc_scan.py reports as without an emitted definition is listed with a
reason: derived impl; compiler-generated builtin item ({Builtin}: drop glue and the like); opaque by flag (in the
config's opaque list); dropped by the tool (non-local, and no emitted definition refers to it); or FAILURE (an emitted
definition refers to it and it has neither a definition nor an external declaration). Reads only.
usage: fv_x2_notemitted.py <run dir> <config.json> <out.tsv>"""
import json, re, sys
from pathlib import Path
RUN, CFG, OUT = Path(sys.argv[1]), json.load(open(sys.argv[2])), sys.argv[3]
pre = json.load(open(RUN / 'result.json'))['lean_prefix']
funs = (RUN / 'lean-src' / (pre + 'Funs.lean')).read_text()
ext = (RUN / 'lean-src' / (pre + 'FunsExternal.lean')).read_text()
code = re.sub(r'(?s)/--.*?-/', '', funs)   # references only, not doc comments
op = [o.replace('crate::', CFG['crate'] + '::') for o in CFG['opaque']]
def opaque(n):
    """same crate, same last segment, and the pattern's module segment occurs in the name"""
    p = n.split('::')
    for o in op:
        q = o.split('::')
        mod = q[-2] if q[-2] != '_' and not q[-2].startswith('{') else q[-3]
        if p[0] == q[0] and p[-1] == q[-1] and mod in p: return True
    return False
rows = []; counts = {}
for crate, f in [(CFG['crate'], 'scan-own.json')] + [(c, 'scan-%s.json' % c) for c in CFG['lib_crates']]:
    d = json.load(open(RUN / 'summaries' / f)); c = counts.setdefault(crate, {'functions_with_body': d['functions_with_body']})
    for m in d['not_emitted']:
        n = m['function']; last = n.split('::')[-1]
        if re.search(r'\{impl\}::(clone|eq|ne|fmt|default|hash)$', n): why = 'derived impl (not emitted; known silent omission)'
        elif '{Builtin}' in n: why = 'compiler-generated builtin item inside the named function (not emitted; known silent omission)'
        elif opaque(n): why = 'opaque by flag (named gap; external declaration in FunsExternal)' if re.search(r'\.%s\b' % re.escape(last), ext) else 'opaque by flag'
        else:
            mod = n.split('::')[-2] if '{impl}' not in n else n.split('::')[-3]
            ref = re.search(r'\b%s\.(?:[A-Za-z0-9_]+\.)?%s\b(?!\.closure)' % (re.escape(mod), re.escape(last)), code)   # a function's own closure (emitted without its parent) is not a reference to it
            why = ('FAILURE: referenced by an emitted definition, no definition or external declaration' if ref else
                   'dropped by the tool: non-local, and no emitted definition refers to it (reachable from the entry only through a named gap)')
        c[why.split(' (')[0].split(':')[0]] = c.get(why.split(' (')[0].split(':')[0], 0) + 1
        rows.append((crate, n, '%s:%s' % (m['file'].split('/src/')[-1] if m['file'] else '', m['line']), m['status'], why))
with open(OUT, 'w') as fo:
    fo.write('crate\tfunction\tfile_line\tscan_status\treason\n')
    for r in rows: fo.write('\t'.join(str(x) for x in r) + '\n')
print(json.dumps(counts, indent=1))
