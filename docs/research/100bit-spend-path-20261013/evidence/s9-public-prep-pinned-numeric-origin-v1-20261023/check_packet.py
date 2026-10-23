from pathlib import Path
import hashlib,json,subprocess,sys
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.stat().st_size==f['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],f['path']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0
 p=r/t['receipt'];q=json.loads(p.read_text());assert q['source_sha256']==t['source_sha256'] and q['object_sha256']==t['object_sha256'];log=p.with_name('lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 if t['module'] not in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs']:assert t['axiom_report_present']
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.llbc','.so','.dylib','.pyc'}
subprocess.run([sys.executable,str(r/'check_origin.py')],check=True)
print('PASS: all9 focused source-pinned numerical rebase targets; source-only receipts and selected numeric dependency owners retained; no release-wide claim')
