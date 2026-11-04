from pathlib import Path
import sys,re,json,hashlib
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True
sys.path.insert(0,str(E.parent/'slice-s-compose10-20261104'))
from NFD_frozen_identity import frozen
shape=json.loads((E/'NFV_K061-shape.json').read_text());h=shape['source']
texts={p:v.decode() for p,v in frozen().items() if p.endswith('.rs')}
rows=[]
for name in re.findall(r'fn (NFO_any_\w+)\(',h):
 ty=name.removeprefix('NFO_any_');found=[(p,t) for p,t in texts.items() if 'pub enum '+ty+' {' in t]
 assert len(found)==1,(ty,len(found))
 p,t=found[0];block=t.split('pub enum '+ty+' {',1)[1].split('\n}',1)[0]
 block=re.sub(r'//[^\n]*','',block)
 variants=set(re.findall(r'^\s*(\w+)\s*(?:,|\(|\{|=)',block,re.M))
 start=h.index('fn '+name+'(');end=h.index('\n',start);body=h[start:end]
 constructors=set(re.findall(re.escape(ty)+r'::(\w+)',body))
 rows.append(dict(type=ty,source=p,variants=sorted(variants),constructors=sorted(constructors),missing=sorted(variants-constructors)))
# Top-level any_error uses the imported short type name.
ty='PoolV1PairForestTerminalFormatErrorV1';found=[(p,t) for p,t in texts.items() if 'pub enum '+ty+' {' in t];assert len(found)==1
p,t=found[0];block=re.sub(r'//[^\n]*','',t.split('pub enum '+ty+' {',1)[1].split('\n}',1)[0]);variants=set(re.findall(r'^\s*(\w+)\s*(?:,|\(|\{|=)',block,re.M));start=h.index('fn any_error(');end=h.index('\n',start);constructors=set(re.findall(ty+r'::(\w+)',h[start:end]));rows.append(dict(type=ty,source=p,variants=sorted(variants),constructors=sorted(constructors),missing=sorted(variants-constructors)))
out=dict(shape_sha256=hashlib.sha256((E/'NFV_K061-shape.json').read_bytes()).hexdigest(),rows=rows,all_variants_covered=all(not r['missing'] for r in rows),classification='syntactic variant coverage; arbitrary numeric/array payloads use kani::any; no new native pass')
(E/'NFV_HELPER_ERROR_COVERAGE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(all_variants_covered=out['all_variants_covered'],types=len(rows),missing=[(r['type'],r['missing']) for r in rows if r['missing']])))
assert out['all_variants_covered']
