#!/usr/bin/env python3
"""PCXQ: textual comparison of the PCXQ_E009 emission blocks with the committed gate blocks (RPu_FIq_Native01..14, evidence/prov-p2b-20261109/inputs/gate).
Normalisation: Source lines removed, namespaces PCXQ_td / FIq_Native / RPu_* -> NS, whitespace collapsed, Aeneas registration attributes removed."""
import re,json,sys,glob,hashlib
sys.dont_write_bytecode=True
SC='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/'
def blocks(s):
    out={}
    for p in re.split(r'(?m)^(?=/-- \[)',s)[1:]:
        m=re.search(r'(?m)^def\s+(\S+)',p)
        if m:out[m.group(1)]=p
    return out
def norm(b):
    b=re.sub(r"(?m)^\s*Source: .*$",'',b);b=re.sub(r"(?m)^\s*(Name pattern|Visibility):.*$",'',b)
    b=re.sub(r'(?m)^@\[[^\n]*\]\n','',b);b=re.sub(r'/--.*?-/','',b,flags=re.S)
    b=re.sub(r'\b(PCXQ_td|FIq_Native|RPu_FIq_Native\d+|AspisR1[A-Za-z0-9]*)\.','NS.',b)
    b=b.replace('aspis_r1_mask_extraction_probe','CRATE').replace('aspis_statement','CRATE').replace('aspis_core.field.','field.').replace('«public»','public1')
    return re.sub(r'\s+','',b)
new=blocks(open('PCXQ_E009_emitted/raw/PCXQ_td/Funs.lean').read())
gate={}
for f in sorted(glob.glob(SC+'gate*.lean')):
    for n,b in blocks(open(f).read()).items():gate.setdefault(n,[]).append((f[-8:-5],b))
T=['validate_transition','semantic_initial_and_absorption','add_schedule_lanes','add_occupancy_lanes','public_digest_packed_selector_tensor','public_digest_packed','semantic_packed','composition_parts','terminal_parts','r0.Public.transition','r0.Public.terminal_qm31']
P='pool_v1.pair_forest_semantic_terminal.'
rows=[]
for t in T:
    n=P+t;g=[(m,b) for k,v in gate.items() for (m,b) in v if k.endswith(n) ]
    nn=new.get(n)
    r=dict(fn=t,emitted=bool(nn),emitted_sha256=nn and hashlib.sha256(norm(nn).encode()).hexdigest(),placeholder=bool(nn and ('sor'+'ry') in nn),gate_modules=[m for m,_ in g])
    if nn and g:
        r['text_identical_modulo_namespace']=[m for m,b in g if norm(b)==norm(nn)]
    if nn and g:
        import difflib
        a=[l for l in nn.splitlines() if 'Source' not in l];b=[l for l in g[0][1].splitlines() if 'Source' not in l]
        r['first_differing_lines']=[l[:120] for l in difflib.unified_diff(b,a,lineterm='',n=0) if l[:1] in '+-' and l[:3] not in('---','+++')][:6]
    rows.append(r);print(r['fn'],r['emitted'],r['gate_modules'],r.get('text_identical_modulo_namespace'))
json.dump(rows,open('PCXQ_td_compare.json','w'),indent=1)
