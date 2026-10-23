from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent;m=json.loads((p/'manifest.json').read_text())
for f in m['files']:
 assert hashlib.sha256((p/f['path']).read_bytes()).hexdigest()==f['sha256'],f['path']
for tag,module,count in [('words','S9CheckedProbeSelectedWordsV1',6),('cm','S9CheckedProbeSelectedCMV1',5)]:
 r=json.loads((p/tag/'evidence/receipt.json').read_text())
 assert r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None
 assert hashlib.sha256((p/tag/'sources'/f'{module}.lean').read_bytes()).hexdigest()==r['source_sha256']
 log=(p/tag/'evidence/lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 audits=re.findall(r'depends on axioms: \[(.*?)\]',log,re.S)
 assert len(audits)+log.count('does not depend on any axioms')==count
 for a in audits:assert set(a.replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert not any(x.suffix in ('.olean','.llbc','.so','.dylib') for x in p.rglob('*'))
print('PASS: eleven checked arithmetic carrier maps with pinned successful focused checks')
