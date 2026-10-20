from pathlib import Path
import json,hashlib,re,subprocess
D=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,f=line.split('  ',1);assert sha(D/f)==h,f
m=json.loads((D/'manifest.json').read_text());assert m['schema']=='focused-extractor-proof-packet-v1'
for target in m['modules']:
 assert sha(D/target['source'])==target['source_sha256']
 rc=json.loads((D/target['receipt']).read_text());e=(D/target['receipt']).parent;pf=json.loads((e/'preflight.json').read_text());cmd=json.loads((e/'command.json').read_text())
 assert rc['exit_status']==0 and rc['process_swaps']==0 and rc['watchdog_abort'] is None
 assert rc['peak_aggregate_rss_bytes']<8*1024**3
 assert rc['object_sha256']==target['object_sha256'] and rc['source_sha256']==target['source_sha256']==pf['source_sha256']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400' and pf['no_dependency_builds']
 for name,pin in pf['direct_imports'].items():assert m['direct_import_source_map'][name]['object_sha256']==pin['sha256']
 text=(e/'lean.log').read_text();assert 'sorryAx' not in text
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text):assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',(D/target['source']).read_text())
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc'] for f in D.rglob('*') if f.is_file())
print('PASS: exact source/import/receipt hashes, focused local caps and standard axioms; no binaries')

subprocess.run(["python3",str(D/"verify_source_reuse.py")],check=True)

