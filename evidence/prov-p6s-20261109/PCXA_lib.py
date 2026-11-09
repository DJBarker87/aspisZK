"""PCXA_lib.py: shared loaders for the P6 snapshot scripts (run via bash wrappers; python3 -I -B)."""
import json, lzma, re, sys, subprocess, collections, importlib.util, functools
sys.dont_write_bytecode = True
SCR = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/part'
EV = '/Users/dominic/ZK/.worktrees/pc-prov-p6s/evidence'
WT = '/Users/dominic/ZK/.worktrees/pc-prov-p6s'
def J(p): return json.load(open(p if p.startswith('/') else f'{EV}/{p}'))
def JX(p): return json.load(lzma.open(p if p.startswith('/') else f'{EV}/{p}'))
spec = importlib.util.spec_from_file_location('PCOP', f'{EV}/prov-p0-20261109/PCO_partition.py')
PCOP = importlib.util.module_from_spec(spec); spec.loader.exec_module(PCOP)
@functools.lru_cache(None)
def lean_index():
    idx = json.load(open(f'{SCR}/lean_index.json')); sha2gid = {}
    for g, v in idx.items(): sha2gid.setdefault(v['sha256'], g)
    return idx, sha2gid
def blob_text(sha):
    idx, sha2gid = lean_index()
    return PCOP.cat_oid(sha2gid[sha]) if False else subprocess.run(['git', '-C', WT, 'cat-file', '-p', sha2gid[sha]], capture_output=True).stdout.decode('utf-8', 'replace')
def decl_segments(text):
    """[(full_name, kind, body_text)] using PCO_partition's declaration regex on comment-stripped text (offsets are valid for the stripped copy)."""
    clean = PCOP.uncomment(text); scope = []; marks = []
    for m in PCOP.DRX.finditer(clean):
        if m[1]: scope.append(('namespace', m[2]))
        elif m[3]:
            if scope: scope.pop()
        elif m[5]: scope.append(('section', ''))
        else:
            if m[6] == 'instance' and m[7] in (':', 'where'): continue
            ns = '.'.join(x[1] for x in scope if x[0] == 'namespace'); nm = m[7]
            full = nm[7:] if nm.startswith('_root_.') else (ns + '.' if ns else '') + nm
            marks.append((m.start(), full, m[6]))
    out = []
    for i, (st, full, k) in enumerate(marks):
        en = marks[i + 1][0] if i + 1 < len(marks) else len(clean)
        out.append((full, k, clean[st:en]))
    return out
WRAP = re.compile(r'wrapping_(add|sub|mul|neg|shl|shr)|\.wrapping')
CHK = re.compile(r'←[^\n]*?\s(\+|-|\*|<<<|>>>)\s')
def arith_class(body):
    w = bool(WRAP.search(body)); c = bool(CHK.search(body))
    return 'MIXED' if (w and c) else 'WRAPPING' if w else 'CHECKED' if c else 'NO_ARITHMETIC'
