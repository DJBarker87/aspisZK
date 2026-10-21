#!/usr/bin/env python3
"""Audit source/receipt agreement and unchanged existing endpoint signatures."""
import hashlib,json,pathlib,re,subprocess
R=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path.cwd(); TREE=ROOT/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
base='b81ae0928'; receipts=[json.loads(p.read_text()) for p in sorted(R.glob('*/receipt.json'))]
for r in receipts:
    d=R/f"{r['module']}-{r['attempt']}"
    assert sha(d/'source.lean')==r['source_sha256']
    assert all(k in r for k in ['argv','source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors'])
    assert r['swaps']==0
    assert r['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
latest={}
for r in receipts:
    if r['module'] not in latest or latest[r['module']]['attempt']<r['attempt']: latest[r['module']]=r
axiom_count=0; finals=[]
for module,r in sorted(latest.items()):
    assert r['exit']==0,(module,r['exit'])
    p=TREE/(module+'.lean'); s=p.read_text(); assert sha(p)==r['source_sha256']
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',s)
    names=re.findall(r'^theorem\s+(\w+)',s,re.M)
    prints=re.findall(r'^#print axioms\s+(\w+)',s,re.M)
    assert sorted(names)==sorted(prints),(module,names,prints)
    log=(R/f"{module}-{r['attempt']}"/'lean.log').read_text()
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|(does not depend on any axioms))",log,re.S)
    assert len(reports)==len(names),(module,reports)
    for name,axes,none in reports:
        assert name.rsplit('.',1)[1] in names
        assert set(filter(None,re.split(r'[\s,]+',axes))) <= {'propext','Classical.choice','Quot.sound'}
    for dep in r['direct_imports']: assert sha(dep['path'])==dep['sha256'],(module,dep['module'],'dependency changed')
    axiom_count+=len(reports)
    finals.append({k:r[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps']})
old=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--',str(TREE.relative_to(ROOT))],text=True).splitlines()
audit=[]
for rel in old:
    name=pathlib.Path(rel).name
    if name.startswith(('R1FinalSoundness','OraclePortHeadline','OraclePortPrefixHeadline','OraclePortMultiHeadline')):
        b=subprocess.check_output(['git','show',base+':'+rel]); now=(ROOT/rel).read_bytes()
        assert b==now,rel
        audit.append(dict(path=rel,base_sha256=hashlib.sha256(b).hexdigest(),current_sha256=sha(ROOT/rel),signature_diff=''))
(R/'signature-audit.json').write_text(json.dumps(dict(base=base,premise_removal_claimed=False,endpoint_files=audit),indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
for rel in changed:
    if rel.endswith('.lean') and '/lean/' in rel:
        assert pathlib.Path(rel).name.startswith('OraclePortRowAware'),rel
summary=dict(schema='rowaware-draft-audit-v1',base=base,modules=len(finals),axiom_reports=axiom_count,attempts=len(receipts),failed_attempts=sum(r['exit']!=0 for r in receipts),swaps=0,unchanged_endpoints=len(audit),finals=finals,release_replay=False)
(R/'audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
