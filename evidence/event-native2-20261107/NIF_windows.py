from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent
pin=json.loads((E/'NIF_FROZEN_INPUT.json').read_text());p=Path(pin['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['archive_sha256']
raw=lzma.decompress(p.read_bytes());assert hashlib.sha256(raw).hexdigest()==pin['raw_sha256'];f=json.loads(raw)
src=f['crates/aspis-r1-cost-probe/src/verifier.rs'];native=(E/'NIF_native.rs.txt').read_text();plan=json.loads((E/'NIF_STAGE_PLAN.json').read_text())
rows=[]
for name,expr in plan.items():
 # Split the original sums and scales only at the named scalar operation.
 kind='line' if name.startswith('line_') else 'circle'
 body=src.split('fn '+kind+'_fold_with_inverses',1)[1].split('\n}',1)[0]
 original={
 'circle_h0_sum':'a.add(b).add(c).add(d)', 'circle_h1_sum':'a.sub(b).sub(c).add(d)',
 'circle_h2_sum':'a.add(b).sub(c).sub(d)', 'circle_h3_sum':'a.sub(b).add(c).sub(d)',
 'line_c0_difference':'a.sub(b)', 'line_c1_difference':'d.sub(c)',
 'line_h1_sum':'c0.add(c1)', 'line_h3_difference':'c0.sub(c1)',
 'circle_h0_scale':'.mul_m31(QUARTER)', 'circle_h1_scale':'.mul_m31(QUARTER.mul(iy))',
 'circle_h2_scale':'.mul_m31(QUARTER.mul(ix))', 'circle_h3_scale':'.mul_m31(QUARTER.mul(ix).mul(iy))',
 'line_h2_scale':'.mul_m31(QUARTER.mul(iz))','line_c0_scale':'.mul_m31(half.mul(ix))',
 'line_c1_scale':'.mul_m31(half.mul(iy))','line_h1_scale':'.mul_m31(half)',
 'line_h3_scale':'.mul_m31(half.mul(iz))','horner_step':'h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))'}[name]
 assert original in body,(name,'frozen span absent')
 assert 'let _out='+expr+';' in native.split('pub fn '+name+'()',1)[1].split('\n',1)[0],name
 rows.append(dict(name=name,expression=expr,original=original,source_sha256=hashlib.sha256(src.encode()).hexdigest(),kind=kind))
# Actual candidate from_fn expression, not a newly substituted decoder.
candidate=f['crates/aspis-r1-cost-probe/src/candidate.rs'];assert 'core::array::from_fn(|s| field(&q[672..800], s))' in candidate
assert 'let _values:[E;4]=core::array::from_fn(|s|field(&bytes,s));' in native
for forbidden in ['static mut','AtomicUsize','RefCell<']:
 assert forbidden not in native
out=dict(stages=rows,fields_source_sha256=hashlib.sha256(candidate.encode()).hexdigest(),qualification='Exact expression windows; native enclosing source-to-effect composition remains separately required')
(E/'NIF_WINDOWS.json').write_text(json.dumps(out,indent=1)+'\n');print('NIF window validation passed:',len(rows),'fold windows plus fields')
