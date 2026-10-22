from pathlib import Path
import hashlib, json, re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
listed={x['path'] for x in m['files']}
for x in m['files']:
 p=D/x['path']; assert p.is_file(),x['path']; assert p.stat().st_size==x['size_bytes']; assert sha(p)==x['sha256'],x['path']
actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in {'manifest.json','check_packet.py'}}
assert actual==listed,({'unlisted':sorted(actual-listed),'missing':sorted(listed-actual)})
assert not any(p.suffix in {'.olean','.ilean','.ir','.o','.llbc'} for p in D.rglob('*') if p.is_file())
mod=m['modules'][0]
rc=json.loads((D/mod['receipt']).read_text()); pf=json.loads((D/mod['preflight']).read_text()); cmd=json.loads((D/mod['command']).read_text())
assert rc['exit_status']==0 and rc['swap_bytes']==0 and rc['object_sha256']==mod['object_sha256']
assert sha(D/mod['source'])==rc['source_sha256_before']==rc['source_sha256_after']==mod['source_sha256']
assert pf['git_head_at_launch']==mod['source_revision']==rc['git_head_at_launch']
assert '-j1' in cmd['argv'] and any(a in {'-M4400','-M=4400'} for a in cmd['argv'])
assert cmd['env']['LEAN_PATH'].startswith('/tmp/d18-v6-width29-coherent-overlay-v2:')
assert sha(D/'cohort/selected-aspisformal-owner-manifest.json')==m['cohort_repair']['overlay_manifest_sha256']
for name,pin in m['direct_import_source_map'].items():
 assert sha(D/pin['source'])==pin['source_sha256'],name
for key in ['propext','Classical.choice','Quot.sound']: assert key in rc['axioms']
log=(D/'evidence/join-lean.log').read_text(); assert 'sorryAx' not in log and 'error:' not in log
reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log); assert len(reports)==1
assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',reports[0]))=={'propext','Classical.choice','Quot.sound'}
for nm in ['cohort-probe','finsum-probe']:
 r=json.loads((D/f'evidence/{nm}-receipt.json').read_text()); assert r['exit_status']==0
print('PASS: s4-width29-literal-join-d18-v1-20261022; explicit head/tail value premises remain open')
