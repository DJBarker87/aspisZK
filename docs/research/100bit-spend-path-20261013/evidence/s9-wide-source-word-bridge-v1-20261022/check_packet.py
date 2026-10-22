from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
for f in m['files']:
 assert hashlib.sha256((p/f['path']).read_bytes()).hexdigest()==f['sha256'],f['path']
assert not any(x.suffix in ('.olean','.llbc','.so','.dylib') for x in p.rglob('*'))
r=json.loads((p/'run/receipt.json').read_text())
assert r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None
assert hashlib.sha256((p/'sources/S9WideSourcePrimitiveBridgeV1.lean').read_bytes()).hexdigest()==r['source_sha256']
l=(p/'run/lean.log').read_text()
assert 'sorryAx' not in l and 'error:' not in l and l.count('depends on axioms:')==6
assert set(re.findall(r'\[(.*?)\]',l,re.S)[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
print('PASS: six standard-axiom reports, pinned source and successful zero-swap receipt')
