"""PW8 shared text helpers. Block split / key / token-normal form are copied from PCXU_mk_newgate.py (prov-p9f-20261110);
xform is PCXU's xform unchanged (rust_* attributes dropped, branch/from_residual/map_err qualified to PCWN_NewLib,
aspis_statement. prefix dropped)."""
import re,hashlib
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
def xform(t):
    t=re.sub(r'(?m)^@\[rust_loop_body\]\n','',t);t=re.sub(r'(?m)^@\[rust_loop\]\n','',t)
    t=re.sub(r',\s*rust_(?:type|const|fun)\s+"[^"]*"','',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry\.branch','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry_traitFromResidualResult\.from_residual','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.map_err','PCWN_NewLib.core.result.Result.map_err',t)
    t=re.sub(r'(?<![\w.])aspis_statement\.pool_v1\.','pool_v1.',t)
    return t
def inner(s,ns):
    a=s.index('namespace '+ns)+len('namespace '+ns);b=s.rindex('end '+ns);return s[a:b]
def blocks(t):
    parts=re.split(r'(?m)^(?=/-- )',t);return [p.strip('\n') for p in parts if p.strip()]
def norm(b):
    b=re.sub(r'(?s)^/--.*?-/\n','',b)
    b=re.sub(r'(?s)@\[(?:[^\[\]]|\[[^\]]*\])*\]','',b)
    b=re.sub(r'(?m)^\s*--.*$','',b)
    return ' '.join(b.split())
def key(b):
    # PW8 change to the PCXU key(): an attribute may sit on the same line as `def` (gate Funs: aspis_core.field.P)
    m=re.search(r'(?m)^(?:@\[[^\]]*\][ \n])?(?:def|structure|inductive|abbrev|axiom|theorem)\s+(\S+)',b)
    if m: return m.group(1)
    m=re.search(r'(?ms)^(?:def|structure|inductive|axiom)\s*\n\s*(\S+)',b);return m.group(1) if m else None
def strip_clashfix(b):
    """Overlay copies of the PIN2 NEWGATE files carry the W3c CLASH-FIX tail after each discriminant inductive; cut it for comparison."""
    i=b.find('\n/- PIN2 W3c');return b if i<0 else b[:i]
def gate_blocks(path,ns='AspisR1PublicPreparationPIN2'):
    g=open(path).read();out={}
    for b in blocks(inner(g,ns)):
        b=strip_clashfix(b);k=key(b)
        if k:out[k]=b
    return out
def strip_disc(b):
    """Cut the hand-expanded discriminant reader/instance tail that the frozen gate Types carries after an inductive
    (gate comment 'Naming-only expansion'); the fresh text carries @[discriminant isize] instead (attributes are not compared)."""
    m=re.search(r'(?m)^(?:--[^\n]*\n)*def \S+\.read_discriminant ',b)
    return b if not m else b[:m.start()].rstrip('\n')
def gate_split(t):
    """Frozen gate blocks: PCXU blocks() plus a split before every undocumented column-0 declaration that follows a blank
    line (the gate Types tail 'Exact newly emitted declarations' carries no doc comments). Module comments /-! -/ dropped."""
    out=[]
    for b in blocks(t):
        for p in re.split(r'\n\n+(?=(?:/-![^\n]*-/\n)?(?:@\[[^\n]*\]\n)?(?:structure|inductive|def|abbrev) )',b):
            p=re.sub(r'(?m)^/-![^\n]*-/\n','',p).strip('\n')
            if p.strip():out.append(p)
    return out
