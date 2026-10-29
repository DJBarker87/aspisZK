"""Receipt/source audit only; no builds or replay of unchanged regression."""
from pathlib import Path
import collections,hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
A=[json.loads(x) for x in (E/'NDM_ATTEMPTS.jsonl').read_text().splitlines()]
assert not (E/'NDM_ACTIVE.json').exists()
counts=collections.Counter(r['kind'] for r in A)
assert counts['kani']==80 and counts['lean']<=80 and counts['extract']<=20
assert len({r['attempt'] for r in A})==len(A)
patch='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
allowed={'propext','Classical.choice','Quot.sound'}
timed=[];classes=collections.Counter();native=[]
for r in A:
 a=r['attempt'];stored=json.loads((E/a/'receipt.json').read_text());assert stored==r
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 for key in ['module','exit_status','wall_seconds','peak_rss_kib','source_revision','print_axioms']:assert key in r
 if r['kind']!='kani':continue
 graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen'] and graph['lock_sha256']==lock
 assert graph['resolved_features_all_crates'] and len(graph['resolved_features_all_crates'])==graph['resolved_packages']
 check=json.loads((E/(a+'-lock-check.json')).read_text());assert check=={'before':lock,'after':lock,'unchanged':True}
 source=json.loads((E/(a+'-source-check.json')).read_text());assert not source['errors']
 assert r['copy_patch_sha256']==patch and r['env']['CARGO_NET_OFFLINE']=='true'
 cmd=r['native_command'];assert 'pool-adapter,private-leaf-salts' in cmd and not any('no-entrypoint' in x for x in cmd)
 text=(E/a/'stdout.log').read_text();lower=text.lower()
 if any(t in lower for t in ['timed out','timeout after','time out']):kind='TIMEOUT';timed.append(a)
 elif 'could not compile' in lower or 'aborting due to' in lower:kind='COMPILE REJECTED'
 elif r['exit_status']==0:kind='PASS'
 else:kind='FAILING CHECK (see semantic/control map)'
 classes[kind]+=1;native.append(dict(attempt=a,target=r['module'],exit=r['exit_status'],classification=kind))
assert timed==['NDM_K006','NDM_K029','NDM_K045','NDM_K067','NDM_K069','NDM_K082'],timed
current=json.loads((E/'NDM_AUDIT_PINS.json').read_text())
accepted=[]
for mod,info in current['active_modules'].items():
 p=E/(mod+'.lean');assert sha(p)==info['source_sha256']
 r=next(r for r in A if r['attempt']==info['attempt']);assert r['exit_status']==0
 for line in r['print_axioms']:
  assert 'sorryAx' not in line
  if '[' in line:assert {x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',')}<=allowed
 assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',p.read_text())
 accepted.append(dict(module=mod,**info))
audit=next(r for r in A if r['attempt']=='NDM_L066');assert audit['exit_status']==0
assert len(audit['print_axioms'])==len(current['top_theorems'])
for line in audit['print_axioms']:
 assert 'sorryAx' not in line
 if '[' in line:assert {x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',')}<=allowed
changed=subprocess.check_output(['git','diff','--name-only','a6366c28f7c514cc2ac66bf687a414f04e2ea503','HEAD'],text=True).splitlines()
assert all(x.startswith('evidence/native-front4b-20261028/') for x in changed)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
out=dict(exit_status=0,budget=dict(counts),native_classification=dict(classes),timeouts=timed,
 accepted_modules=accepted,axioms_audit=dict(attempt='NDM_L066',declarations=len(audit['print_axioms']),
 own_theorems=sum(n.startswith('NDM_') for n in current['top_theorems']),allowed=sorted(allowed)),
 peak_rss_kib=max(int(r['peak_rss_kib']) for r in A),swaps=0,source_changes='own evidence only',
 no_full_release_or_manifest_replay=True,shipped_files_changed=False,elf_rebuild_trigger=False,
 native_attempts=native,baseline_revision='a6366c28f7c514cc2ac66bf687a414f04e2ea503')
(E/'NDM_FINAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['accepted_modules','native_attempts']},indent=2))
