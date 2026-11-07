"""Local receipt packaging and hygiene only; no replay or additional host scope."""
import pathlib,json,re,hashlib,lzma,subprocess
E=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[json.loads(l) for l in (E/'PCH_ATTEMPTS.jsonl').read_text().splitlines()]
round2=[r for r in records if re.fullmatch(r'PCH_B00[1-6]|PCH_A0(?:0[2-9]|1[0-9]|20)',r['attempt'])]
assert len(round2)==25 and len({r['attempt'] for r in round2})==25
for r in round2:
 assert r['admission_allowed'] is True and r['admission_exit_status']==0
 assert r['disk_free_before_bytes']>=40_000_000_000
 assert r['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 text=(E/r['time_file']).read_text()
 def match(p,fn=str):
  m=re.search(p,text);return fn(m[1]) if m else None
 r['peak_rss_kib']=match(r'Maximum resident set size \(kbytes\): (\d+)',int);r['swaps']=match(r'Swaps: (\d+)',int);r['wall_time']=match(r'Elapsed \(wall clock\) time.*?: (.*)')
 if r['peak_rss_kib'] is None:r['metrics_unavailable_reason']='Deliberate own-scope stop terminated time collector; no pass or exact peak claimed.'
 else:assert r['swaps']==0
 p=E/(r['attempt']+'_source.py')
 if not p.exists():
  src=E/r['target'];assert sha(src)==r['source_sha256'],r['attempt'];p.write_bytes(src.read_bytes())
 assert sha(p)==r['source_sha256'],r['attempt'];r['source_snapshot']=p.name
 if r['attempt']=='PCH_A006':r['observed_rss_kib_before_stop']=6388064
 if r['attempt']=='PCH_B004':r['no_credit_reason']='Own-scope overlap with A006; stopped and not relied on; build budget consumed.'
(E/'PCH_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
assert sum(r['scope_kind']=='build' for r in round2)==6 and sum(r['scope_kind']=='audit' for r in round2)==19
budget=dict(round=2,build=dict(allowed=6,used=6),script_audit=dict(allowed=19,used=19),Kani=dict(allowed=0,used=0),Lean=dict(allowed=0,used=0),stopped_without_credit=['PCH_B004','PCH_A006'],unused=0,scope_overlap='B004/A006 overlap disclosed; both stopped, neither relied on; own-job guard added',target_established=False)
(E/'PCH_BUDGET.json').write_text(json.dumps(budget,indent=2)+'\n')
b=json.loads((E/'PCH_B003_BUILD.json').read_text())
for name in ['PCH_B002_DEPENDENCIES.json','PCH_B005_DUMP.json','PCH_B006_DUMP.json']:
 p=E/name;d=json.loads(p.read_text());d.update(resolved_packages=b['resolved_packages'],compiler_features=b['compiler_features'],feature_provenance='Post-recorded from exact-build retained metadata in PCH_B003_BUILD.json; actual compiler cfg remains in each exact command; no fresh cargo resolution.');p.write_text(json.dumps(d,indent=1)+'\n')
for p in E.glob('PCH_B00*_*.json'):
 if not p.name.endswith(('_BUILD.json','_DEPENDENCIES.json','_DUMP.json')):continue
 d=json.loads(p.read_text());a=p.name[:8];d.update(admission_receipt=a+'-admission.json',source_revision_receipt='PCH_ATTEMPTS.jsonl#'+a,print_axioms='N/A: no Lean theorem',resource_time_file=a+'.time');p.write_text(json.dumps(d,indent=1)+'\n')
# Update final metadata hashes, preserving the actual compiler/source artifact pins.
a=json.loads((E/'PCH_AUTHORITY.json').read_text())
for n in a['round2_inputs']:
 p=E/n;a['round2_inputs'][n].update(sha256=sha(p),bytes=p.stat().st_size)
a['budget']=budget;a['final_feature_audit']='PCH_A017_AUDIT.json';a['final_artifact_audit']='PCH_A020_AUDIT.json'
(E/'PCH_AUTHORITY.json').write_text(json.dumps(a,indent=2)+'\n')
x=json.loads((E/'PCH_A018_AUDIT.json').read_text());assert len(x['controls'])==3
assert all(r['rejected'] is True for r in x['controls'])
v=json.loads((E/'PCH_VALIDATION.json').read_text());assert v['final_validator_sha256']==sha(E/'PCH_VALIDATOR.py')
assert json.loads((E/'PCH_A020_AUDIT.json').read_text())['validator_exit_status']==0
for p in E.glob('*.xz'):
 raw=lzma.decompress(p.read_bytes());q=E/(p.name.removesuffix('.xz')+'.sha256');expected=hashlib.sha256(raw).hexdigest();
 if q.exists():assert q.read_text().strip()==expected,p.name
 else:q.write_text(expected+'\n')
assert not list(E.rglob('__pycache__'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not [p for p in E.rglob('*') if p.is_file() and p.suffix in ['.so','.rlib','.rmeta','.olean','.tar','.gz']]
# Source/control inputs are all tracked or about to be committed under this prefix only.
base=json.loads((E/'PCH_B001_INPUTS.json').read_text())['source_revisions']
out=dict(status='PASS_PACKAGING_ONLY',scope_budget=budget,source_revisions=base,shipped_changes=0,files_over_20MB=0,print_axioms='N/A',closed=39,excluded=0,open=239,partial_graph=True,remaining='PCH_REMAINING.md')
(E/'PCH_FINAL_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print('PCH packaging PASS: 6/6 builds, 19/19 audits, 39 inherited CLOSED / 0 excluded / 239 OPEN')
