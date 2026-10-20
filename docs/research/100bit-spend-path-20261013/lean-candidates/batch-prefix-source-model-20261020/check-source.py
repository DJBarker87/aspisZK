from pathlib import Path
import json,subprocess,hashlib,re
p=Path(__file__).resolve().parent
r=next(q for q in p.parents if (q/'.git').exists())
sha=lambda b:hashlib.sha256(b).hexdigest()
e=p/'extraction/indexed-candidate';pins=json.loads((e/'input/source-pins.json').read_text())
for c in pins['cuts']:
 raw=subprocess.check_output(['git','show',pins['revision']+':'+c['path']],cwd=r)
 b=raw[c['start_byte']:c['end_byte_exclusive']]
 assert sha(b)==c['sha256']
 assert b==(e/'input/fragments/prefix.rs').read_bytes()
s=(p/'diagnostics/extraction-v1/input/lib.rs').read_text()
s=s.replace('for &value in &flat {prefixes.push(product);product=product.mul(value);}',
 'let mut i=0usize;\n        while i<flat.len() {prefixes.push(product);product=product.mul(flat[i]);i+=1;}')
assert s==(e/'input/lib.rs').read_text()
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
g=e/'generated/AspisR1BatchPrefix'
assert clean((g/'Types.lean').read_text())==(p/'sources/AspisR1BatchPrefix/Types.lean').read_text()
s=clean((g/'Funs.lean').read_text()).replace('import AspisR1BatchPrefix.FunsExternal\n','')
for n in ['prefix_product_loop.body','prefix_product_loop','prefix_product']:
 s=s.replace('def '+n+'\n','def '+n+'\n  (mul : field.M31 → field.M31 → Result field.M31)\n')
s=s.replace('field.M31.mul','mul').replace('prefix_product_loop.body flat','prefix_product_loop.body mul flat').replace('prefix_product_loop flat','prefix_product_loop mul flat')
assert s==(p/'sources/BatchPrefixExplicitMul.lean').read_text()
m=json.loads((p/'manifest.json').read_text())
for x in m['modules']:
 assert sha((p/x['source']).read_bytes())==x['source_sha256']
 rc=json.loads((p/x['receipt']).read_text());assert rc['exit_status']==0 and rc['scope_swap_peak_bytes']==0
 assert 'sorryAx' not in (p/Path(x['receipt']).parent/'lean.log').read_text()
print('PASS: frozen original span, precisely identified indexed Rust candidate, explicit-mul-only emitted Lean adapter, selected green target pins')
