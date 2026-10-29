"""Exact source expansion of every add_value_lanes loop and read helper site."""
from pathlib import Path
import re,json,hashlib,sys
# Reuse only lexical and balanced-body helpers, not the other script's writes.
ns={};s=Path('tools/pv-b3p6-20261028/source_unroll227_resume10.py').read_text();exec(s[:s.index('rows=[]')],ns)
extract,toks=ns['extract'],ns['toks'];P=Path('tools/pv-b3p6-20261028/v244');O=Path('evidence/pv-b3p6-20261028/resume10')
a=extract((P/'host_terminal.rs').read_text(),'add_value_lanes');b=extract((P/'reference_terminal.rs').read_text(),'add_value_lanes');expanded=a;loops=[]
for block in range(3):
 m=re.search(r'while index < 10\s*\{([^{}]*)\}',expanded);assert m
 inner=m[1];assert inner.count('index += 1;')==1;inner=inner.replace('index += 1;','')
 replacement='\n'.join(re.sub(r'\bindex\b',str(i)+'usize',inner)for i in range(10))
 expanded=expanded[:m.start()]+replacement+expanded[m.end():];loops.append(dict(loop=block,iterations=list(range(10)),body=inner.strip()))
m=re.search(r'for residual in &mut range\s*\{([^{}]*)\}',expanded);assert m
assert toks(m[1])==toks('*residual = range_selector.mul(*residual);')
replacement='\n'.join(f'range[{i}usize] = range_selector.mul(range[{i}usize]);'for i in range(33));expanded=expanded[:m.start()]+replacement+expanded[m.end():]
loops.append(dict(loop=3,iterations=list(range(33)),body=m[1].strip(),frame='only selected range element is replaced, other elements retained'))
readsites=re.findall(r'read227\(\s*([\w.]+)\s*,\s*(\d+)usize\s*\)',b);assert len(readsites)==93,len(readsites)
normalized=re.sub(r'read227\(\s*([\w.]+)\s*,\s*(\d+)usize\s*\)',r'\1[\2usize]',b)
normalized=re.sub(r'let mut residual_index = 0usize\s*;','',normalized)
assert toks(expanded)==toks(normalized)
record=dict(body='add_value_lanes',source_body_sha256=hashlib.sha256(a.encode()).hexdigest(),owned_body_sha256=hashlib.sha256(b.encode()).hexdigest(),loops=loops,read_helper_sites=len(readsites),ordered_source_token_roundtrip=True,read_law='PV_B3P_Binding10227.add_value_read_binding10 (when accepted)',read_CSE='source repeats thirty immutable reads across square calls; named deterministic-read law required and separately supplied',credit='complete source token expansion check plus emitted read binding; actual source-loop-to-emission/frame/stdlib binding still requires composition',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'value-source-check.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(loops=len(loops),read_helper_sites=len(readsites),exact_tokens=True)))
