"""Read-only evidence audit for this job; no builds, source rewrites or host launches."""
from pathlib import Path
import collections,hashlib,json,re,subprocess
P=Path(__file__).resolve().parent; R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('BEl_*/receipt.json'))]
bykind=collections.Counter(j['kind'] for j in receipts)
assert bykind['lean']<=100 and bykind['kani']==20
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for j in receipts:
 assert j['limits']==limits,j['attempt']
 assert str(j['swaps'])=='0',j['attempt']
 assert j.get('source_hashes'),j['attempt']
 assert j.get('source_revision') and j.get('deps_fingerprint'),j['attempt']
 assert all(k in j for k in ['wall_seconds','exit_status','peak_rss_kib','print_axioms']),j['attempt']
valid_kani=[]; invalid_kani=[]
for j in receipts:
 if j['kind']!='kani':continue
 log=(P/j['attempt']/'stdout.log').read_text()
 valid=j['exit_status']==0 and log.count('VERIFICATION SUCCESSFUL')==1 and 'VERIFICATION FAILED' not in log
 (valid_kani if valid else invalid_kani).append(j['attempt'])
assert len(valid_kani)==len(invalid_kani)==10
modules={}
for source in sorted((R/'lean').glob('BEl_*.lean')):
 candidates=[j for j in receipts if j['kind']=='lean' and j.get('source_hashes',{}).get(source.name)==sha(source) and j['exit_status']==0]
 assert candidates,source
 j=candidates[-1]
 log=(P/j['attempt']/'stdout.log').read_text()
 assert 'sorryAx' not in log,source
 assert not re.search(r'^\s*(axiom|sorry|admit)\b|native_decide|maxHeartbeats|maxRecDepth',source.read_text(),re.M),source
 for theorem in re.findall(r'^theorem\s+(\w+)',source.read_text(),re.M):
  assert re.search(r'#print axioms\s+'+theorem+r'\b',source.read_text()),(source,theorem)
 modules[source.name]={'source_sha256':sha(source),'receipt':j['attempt'],'print_axioms':j['print_axioms']}
baseline=json.loads((P/'BEl_BASELINE.json').read_text())
for name,h in baseline['files'].items():assert sha(R/name)==h,name
# All changes outside this prefix/evidence directory are forbidden.
changed=subprocess.check_output(['git','diff','--name-only',baseline['revision']],cwd=R,text=True).splitlines()
assert all(n.startswith('evidence/l166-proof4-20261027/') or (n.startswith('lean/BEl_') and n.endswith('.lean')) for n in changed)
assert not any(Path(n).suffix in ['.olean','.llbc','.so','.elf','.a','.o','.tar','.gz'] for n in changed)
old=(P/'BEl_K21/sources/BEl_rust/src/BEl_reference.rs').read_text()
expanded=(P/'BEl_rust/src/BEl_reference.rs').read_text().replace('include!("BEl_owned.rs");',(P/'BEl_rust/src/BEl_owned.rs').read_text().rstrip())
tokens=lambda s:re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
assert tokens(old)==tokens(expanded)
# Same literal root binders; old conclusion retained before adding reference facts.
before=(R/'lean/Rc10_Top.lean').read_text().split('theorem deployed',1)[1].split(' := by',1)[0]
after=(R/'lean/BEl_Top.lean').read_text().split('theorem deployed',1)[1].split(' := by',1)[0]
oldhead,oldconclusion=before.split('    :\n',1)
newhead,newconclusion=after.split('    :\n',1)
assert oldhead==newhead
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(newconclusion).startswith('('+normalize(oldconclusion)+')∧BEl_Packet.Facts')
# Independently re-enumerate the atomic ledger, counting aliases once.
rows=json.loads((R/'evidence/l166-proof3-20261026/BEk_ledger_rows.json').read_text())
actual=collections.Counter(x['classification'] for x in rows if x['scope']=='actual antecedent')
deployment=collections.Counter(x['classification'] for x in rows if x['scope'] in ['actual antecedent','deployment only'])
assert dict(actual)=={'T':83,'P':12,'G':13}
assert dict(deployment)=={'T':89,'P':16,'G':13}
assert next(x for x in rows if x['id']=='L166')['status']=='retained'
result={'status':'PASS; reference-only result, physical L166 remains open','budget':dict(bykind),
 'verified_kani':valid_kani,'excluded_kani':invalid_kani,'modules':modules,
 'source_identity':baseline['files'],'unchanged_root_binders':True,
 'old_conclusion_retained':True,'extra_conclusion':'BEl_Packet.Facts (reference computed packet)',
 'actual_before':dict(actual),'actual_after':dict(actual),'deployment_before':dict(deployment),'deployment_after':dict(deployment),
 'premise_delta':0,'no_added_trust':True,'L166_removed':False,
 'K21_core_tokens_unchanged_after_include_extraction':True,
 'old_root_source_sha256':sha(R/'lean/Rc10_Top.lean'),'latest_top_source_sha256':sha(R/'lean/BEl_Top.lean')}
(P/'BEl_validation.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'BEl_attempts.jsonl').write_text(''.join(json.dumps(j,sort_keys=True)+'\n' for j in receipts))
print(json.dumps({k:v for k,v in result.items() if k not in ['modules','source_identity']},indent=2))
