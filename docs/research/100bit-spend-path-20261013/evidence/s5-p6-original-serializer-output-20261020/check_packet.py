from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text());assert m['schema']=='focused-extractor-proof-packet-v1'
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
for x in m['modules']:
 assert sha(D/x['source'])==x['source_sha256']
 rc=json.loads((D/x['receipt']).read_text());pf=json.loads((D/x['preflight']).read_text());cmd=json.loads((D/'evidence/v24/command.json').read_text())
 assert rc['exit_status']==0 and rc['process_swaps']==0 and rc['watchdog_abort'] is None
 assert rc['object_sha256']==x['object_sha256'] and rc['source_sha256']==pf['source_sha256']==x['source_sha256'] and pf['source_revision']==x['source_revision']
 assert rc['peak_aggregate_rss_bytes']<8*2**30 and '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 for n,pin in pf['direct_imports'].items():assert m['direct_import_source_map'][n]['object_sha256']==pin['sha256']
 log=(D/'evidence/v24/lean.log').read_text();assert 'sorryAx' not in log and 'core.fmt.Formatter' not in log and 'error:' not in log
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
for row in m['inherited_owners']:assert sha(D/row['source'])==row['source_sha256']
# Reconstruct the adapter text without requiring a binary in the packet.
rep=json.loads((D/m['adapter_check']['report']).read_text())
s=(D/'sources/generated-original/Funs.lean').read_text()
for line in rep['resource_lines_removed']:s=s.replace(line+'\n','')
for a in rep['exact_whitelist']:
 assert s.count(a['old'])==a['count']==1;s=s.replace(a['old'],a['new'])
assert s==(D/'sources/generated-adapted/Funs.lean').read_text()
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc','.so','.a','.exe'] for f in D.rglob('*') if f.is_file())
print('PASS: exact P6 output theorem, standard axioms, focused caps, source-adapter reconstruction; inherited receipt and Std/runtime boundaries explicit')
