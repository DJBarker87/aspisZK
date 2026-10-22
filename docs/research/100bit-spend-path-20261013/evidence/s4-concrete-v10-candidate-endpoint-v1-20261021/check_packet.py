from pathlib import Path
import hashlib,json,re,subprocess
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
for f in m['files']:
 p=D/f['path']; assert p.is_file() and sha(p)==f['sha256'] and p.stat().st_size==f['size_bytes'],f['path']
mod=m['modules'][0]; rc=json.loads((D/mod['receipt']).read_text()); pf=json.loads((D/mod['preflight']).read_text())
assert rc['exit_status']==0 and rc['watchdog_abort'] is None and rc['process_swaps']==0
assert rc['source_sha256']==mod['source_sha256']==sha(D/mod['source'])==pf['source_sha256']
assert rc['object_sha256']==mod['object_sha256'] and rc['source_revision_at_launch']==mod['source_revision']==m['source_revision_at_launch']
assert rc['peak_aggregate_rss_bytes']==mod['peak_aggregate_rss_bytes']<8*2**30
assert rc['wall_seconds']==mod['wall_seconds']
assert pf['lean_sha256']==m['compiler']['sha256'] and pf['lean']==m['compiler']['path']
assert '-j1' in json.loads((D/mod['command']).read_text())['argv']
for name,owner in m['direct_import_source_map'].items():
 src=D/owner['source']; assert sha(src)==owner['source_sha256'],name
 pm=json.loads((D/owner['producer_manifest']).read_text()); pr=json.loads((D/owner['producer_receipt']).read_text())
 po=next(x for x in pm['modules'] if x['module']==name)
 assert po['source_sha256']==owner['source_sha256']==pr['source_sha256']
 assert po['object_sha256']==owner['object_sha256']==pr['object_sha256'] and pr['exit_status']==0
assert set(m['direct_import_source_map'])==set(pf['direct_imports'])
for name,pin in pf['direct_imports'].items(): assert m['direct_import_source_map'][name]['object_sha256']==pin['sha256']
log=(D/'evidence/lean.log').read_text(); reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log)
assert len(reports)==1 and set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',reports[0]))=={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and 'error:' not in log
for key,hashkey in (('candidate_rust_source','candidate_rust_sha256'),('v6_rust_source','v6_rust_sha256'),('v6_generated_funs','v6_generated_funs_sha256'),('source_body_checker','source_body_checker_sha256'),('extraction_checker','extraction_checker_sha256')):
 p=D/m['source_correspondence'][key]; assert sha(p)==m['source_correspondence'][hashkey]
assert 'frozen Rust refinement' in m['source_correspondence']['scope']
repo=D.parents[4]
for script in ('docs/research/100bit-spend-path-20261013/lean-candidates/s4-minimal-fixed-calls-v10-20261021/check-source-correspondence.py','docs/research/100bit-spend-path-20261013/lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/check-extraction.py'):
 r=subprocess.run(['python3',str(repo/script)],capture_output=True,text=True)
 assert r.returncode==0,(script,r.stdout,r.stderr)
print('PASS: s4-concrete-v10-candidate-endpoint-v1-20261021; candidate source/body evidence only; upstream caller and frozen-Rust/Std refinement remain open')
