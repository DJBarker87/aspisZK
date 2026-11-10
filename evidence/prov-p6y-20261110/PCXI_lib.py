# PCXI_lib.py: Rust item extraction, normalisation, frozen lookup (helper for PCXI_compare.sh)
import re, hashlib

def strip_comments(t):
    out = []; i = 0; n = len(t); st = 0
    while i < n:
        c = t[i]
        if t.startswith('//', i):
            while i < n and t[i] != '\n': i += 1
            continue
        if t.startswith('/*', i):
            d = 1; i += 2
            while i < n and d:
                if t.startswith('/*', i): d += 1; i += 2
                elif t.startswith('*/', i): d -= 1; i += 2
                else: i += 1
            out.append(' '); continue
        if c == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            out.append(t[i:j + 1]); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)

def norm(t):
    t = strip_comments(t)
    t = re.sub(r'\s+', ' ', t).strip()
    t = re.sub(r'\s*([{}();,:<>\[\]=+\-*/%&|!^.])\s*', r'\1', t)
    return t

def match_end(t, i, open_c='{', close_c='}'):
    d = 0; n = len(t)
    while i < n:
        c = t[i]
        if c == '"':
            i += 1
            while i < n and t[i] != '"': i += 2 if t[i] == '\\' else 1
        elif c == "'" and i + 2 < n and (t[i + 2] == "'" or (t[i + 1] == '\\')):
            j = t.find("'", i + 2); i = j if j > 0 else i
        elif c == open_c: d += 1
        elif c == close_c:
            d -= 1
            if d == 0: return i
        i += 1
    return -1

def impl_blocks(t):
    # returns list of (owner_names, start, end) for impl blocks
    res = []
    for m in re.finditer(r'\bimpl\b[^{;]*\{', t):
        hdr = m.group(0)
        e = match_end(t, m.end() - 1)
        if e < 0: continue
        names = set(re.findall(r'\b([A-Z][A-Za-z0-9_]*)\b', re.sub(r'<[^>]*>', '', hdr)))
        res.append((names, m.start(), e))
    return res

def with_attrs(t, s):
    # extend start s backwards over attribute lines / doc comments
    lines_start = t.rfind('\n', 0, s) + 1
    cur = lines_start
    while cur > 0:
        prev_end = cur - 1
        prev_start = t.rfind('\n', 0, prev_end) + 1
        ln = t[prev_start:prev_end].strip()
        if ln.startswith('#[') or ln.startswith('#!['):
            cur = prev_start
        else: break
    return cur

def find_items(t, kind, name, owner=None):
    """return list of raw item texts (with attrs) of kind in text; kind in fn/const/type"""
    res = []
    impls = impl_blocks(t)
    if kind == 'fn':
        pat = r'\bfn\s+' + re.escape(name) + r'\b'
    elif kind == 'const':
        pat = r'\b(?:const|static)\s+' + re.escape(name) + r'\b'
    else:
        pat = r'\b(?:struct|enum|type)\s+' + re.escape(name) + r'\b'
    for m in re.finditer(pat, t):
        s = m.start()
        # include leading pub etc on same line
        ls = t.rfind('\n', 0, s) + 1
        pre = t[max(ls, s - 60):s]
        mm = re.search(r'((pub(\([a-z:]+\))?\s+)?(unsafe\s+)?(const\s+)?(extern\s+"C"\s+)?(#\[inline[^\]]*\]\s*)?)$', pre)
        s2 = s - len(mm.group(1)) if mm else s
        at_line_start = (t[ls:s2].strip() == '')  # s2 >= s-60
        inowner = None
        for names, a, b in impls:
            if a < s < b: inowner = names
        if owner is not None and (inowner is None or owner not in inowner): continue
        if owner is None and inowner is not None and kind == 'fn':
            # method inside impl but queried as free fn: still allow only if no owner info
            pass
        # end
        if kind in ('fn',):
            j = s
            while j < len(t) and t[j] not in '{;': j += 1
            if j < len(t) and t[j] == '{': e = match_end(t, j)
            else: e = j
        elif kind == 'const':
            j = s; d = 0
            while j < len(t):
                if t[j] in '([{': d += 1
                elif t[j] in ')]}': d -= 1
                elif t[j] == ';' and d == 0: break
                j += 1
            e = j
        else:
            j = s
            while j < len(t) and t[j] not in '{;(': j += 1
            if j < len(t) and t[j] == '{': e = match_end(t, j)
            elif j < len(t) and t[j] == '(':
                e2 = match_end(t, j, '(', ')'); k = t.find(';', e2); e = k
            else: e = j
        a0 = with_attrs(t, ls) if at_line_start else s2
        res.append(t[a0:e + 1])
    return res

def parse_rust_path(rp):
    """CRATE::a::{CRATE::a::T}::m  -> (kind_guess, owner, name, module_segments)"""
    owner = None
    m = re.search(r'\{[^{}]*::([A-Za-z0-9_]+)\}', rp)
    if m: owner = m.group(1)
    p = re.sub(r'\{[^{}]*\}::', '', rp)
    segs = [s for s in p.split('::') if s != 'CRATE']
    closure = False
    while segs and (segs[-1] == 'closure' or re.fullmatch(r'closure\d*|loop\d*', segs[-1])):
        segs.pop(); closure = True
    name = segs[-1] if segs else ''
    return owner, name, segs[:-1], closure

def calls(t):
    return set(re.findall(r'\b([a-z_][a-z0-9_]*)\s*\(', t))
