from pathlib import Path
import json,re,subprocess,hashlib,csv
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029';base='65a5f8ecf3ea29c7c919eb5298edab247729f261'
records=[dict(attempt=int(p.stem.split('-')[-1]),**v) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
with (E/'verification.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','deps_fingerprint','accepted','print_axioms'])
 for v in records:w.writerow([v[k] for k in ['attempt','module','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','deps_fingerprint','accepted']]+[' | '.join(v['axioms'])])
expected=json.loads((E/'axioms-expected.json').read_text());audits=[];allowed={'propext','Classical.choice','Quot.sound'}
for v in expected:
 r=next(x for x in records if x['attempt']==v['attempt']);assert r['accepted'],v['module']
 names=[];bad=[]
 for line in r['axioms']:
  m=re.match(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",line)
  if m:
   names.append(m[1]);axioms=set((m[2] or '').split(', '))-{''}
   if not axioms<=allowed:bad.append(dict(line=line,unexpected=sorted(axioms-allowed)))
 assert sorted(names)==sorted(v['names']),(v['module'],set(v['names'])-set(names),set(names)-set(v['names']))
 assert not bad,bad
 audits.append(dict(module=v['module'],attempt=v['attempt'],names=names,unexpected_axioms=bad,accepted=True))
(E/'axioms-audit.json').write_text(json.dumps(audits,indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed_paths=('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_','evidence/pv-runjoin63-20261029/','tools/pv-runjoin63-20261029/')
assert all(p.startswith(allowed_paths) for p in changed),[p for p in changed if not p.startswith(allowed_paths)]
protected=['PV_RunJoin_ActualProvenance60.lean','PV_RunJoin_PublishProduced60.lean','PV_RunJoin_PublishContext57.lean','PV_RunJoin_PublishSkeleton54.lean','PV_RunJoin_CaptureFactorSource60.lean','PV_RunJoin_CapturedTransport60.lean']
checks=[]
for name in protected:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name
 b=subprocess.check_output(['git','show',base+':'+p]);current=(R/p).read_bytes();assert b==current
 checks.append(dict(path=p,sha256=hashlib.sha256(current).hexdigest(),unchanged=True))
(E/'boundaries.json').write_text(json.dumps(dict(entry_revision=base,checked_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),changed_paths=changed,protected=checks,ledger_edited=False,implementation_edited=False,trust_fields_added=0,rows_removed=[],link_bodies_changed=False),indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
print('records',len(records),'audit declarations',sum(len(v['names']) for v in audits),'boundaries unchanged')
