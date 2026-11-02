from pathlib import Path
import json,hashlib,importlib.util
D=Path(__file__).parent
spec=importlib.util.spec_from_file_location('pv_source',D/'PV_O11_source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
items=[('std-error.rs','pub fn kind(&self)'),('std-repr-bitpacked.rs','pub(super) fn data(&self)'),('std-repr-bitpacked.rs','unsafe fn decode_repr<'),('std-repr-bitpacked.rs','fn kind_from_prim('),('std-unix-error.rs','pub fn decode_error_kind(')]
rows=[]
for f,anchor in items:
 a=(D/'inputs'/f).read_text();b=(D/'inputs'/('extractor-'+f)).read_text();aa=m.body(a,anchor);bb=m.body(b,anchor) if anchor in m.strip(b) else None
 rows.append(dict(file=f,anchor=anchor,deployed_source_sha256=hashlib.sha256(a.encode()).hexdigest(),extractor_source_sha256=hashlib.sha256(b.encode()).hexdigest(),deployed_body=aa,extractor_body=bb,token_equal=bb is not None and m.tok(aa)==m.tok(bb)))
p=D/'PV_O11_std-parity.json';p.write_text(json.dumps(dict(deployed='1.94.1',extractor='nightly-2026-06-01',items=rows,all_token_equal=all(x['token_equal'] for x in rows),scope='five named bodies only; not a complete reached-std closure and not native/refinement credit. Dynamic-trait translation failed; pointer arithmetic/load helpers and ErrorKind interpretation remain.'),indent=2)+'\n');print([(x['anchor'],x['token_equal']) for x in rows])
