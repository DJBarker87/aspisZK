#!/usr/bin/env python3
"""Read-only source/evidence audit. No compiler or private-cache replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claims-row-step-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
reuse=json.loads((P/'source-reuse.json').read_text())['files']
cache={}
def sha(p):
 if p.is_file():return hashlib.sha256(p.read_bytes()).hexdigest()
 row=reuse[str(p.relative_to(P))]
 oid=subprocess.check_output(['git','-C',str(R),'rev-parse',row['revision']+':'+row['path']],text=True).strip()
 assert oid==row['git_blob']
 if oid not in cache:cache[oid]=hashlib.sha256(subprocess.check_output(['git','-C',str(R),'cat-file','blob',oid])).hexdigest()
 assert cache[oid]==row['sha256']
 return cache[oid]
for root in [P,P/'extra']:
 m=json.loads((root/'manifest.json').read_text())
 for rel,h in m['files'].items():assert sha(root/rel)==h,(root,rel)
assert not any(p.suffix in ['.olean','.ir','.llbc','.rlib','.rmeta','.so','.a','.o','.pyc'] for p in P.rglob('*') if p.is_file())
D=P/'attempts/claims_row_write_preserves_initialized_prefix-v6';r=json.loads((D/'receipt.json').read_text());i=json.loads((D/'input.json').read_text())
assert r['exit_status']==0 and r['swaps']==0 and r['cgroup_swap_current']==0
assert r['limits']['memory.max']==str(2*2**30) and r['limits']['memory.swap.max']=='0'
assert all(r['sources_unchanged'].values()) and all(r['workspace_unchanged'].values()) and r['native_imports_unchanged']
assert sha(D/'input.json')==r['input_sha256']
assert '--unwinding-assertions' in r['command'] and 'uninit-checks' not in r['command']
log=(D/'stdout.log').read_text();assert '0 of 769 failed' in log and '3 of 3 cover properties satisfied' in log and 'VERIFICATION:- SUCCESSFUL' in log
assert i['environment']['RUSTFLAGS'].startswith('-C opt-level=3 ')
for name,h in i['workspace_pins'].items():assert sha(P/name)==h,name
for dep in (P/'dependencies').iterdir():
 meta=json.loads((dep/'source-root.json').read_text())
 for rel,h in i['source_pins'][meta['manifest']].items():assert sha(dep/rel)==h,(dep,rel)
source=(P/'proofs.rs').read_text();assert source==(R/'tools/s1-claims-row-step-20261024/proofs.rs').read_text()
assert 'kani::assume' not in source and source.count('#[kani::stub(')==1
for t in ['Box::new(MaybeUninit::<Claims>::uninit())','out.assume_init()','record.decode_k::<29>(p * 29)?','assert_eq!(CALLS,0)','assert_eq!(offset_values,OFFSET)','assert_eq!(record.framed().as_ptr(),RECORD_PTR)','assert_eq!(record.framed().len(),RECORD_LEN)']:assert t in source,t
binding=json.loads((P/'source-binding.json').read_text());assert sha(P/'proofs.rs')==binding['proof_sha256']
for name,row in binding['frozen_files'].items():
 assert sha(P/'payload'/name)==row['sha256']
 assert hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',binding['revision']+':'+row['path']])).hexdigest()==row['sha256']
normalize=lambda s:''.join(s.split());assert normalize(binding['fragment']) in normalize(source) and normalize(binding['fragment']) in normalize((P/'payload/r1_semantic.rs').read_text())
for tag in ['uninit-full','uninit-min']:
 d=P/'extra'/tag;rr=json.loads((d/'attempt/receipt.json').read_text());ii=json.loads((d/'attempt/input.json').read_text())
 assert rr['exit_status']==1 and rr['swaps']==0 and rr['cgroup_swap_current']==0
 assert 'uninit-checks' in rr['command'] and sha(d/'attempt/input.json')==rr['input_sha256']
 assert 'FieldsShape::Primitive with a different ABI than ValueAbi::Scalar' in (d/'attempt/stdout.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' not in (d/'attempt/stdout.log').read_text()
for phase in ['charon','aeneas']:
 d=P/'extra'/phase;rr=json.loads((d/'receipt.json').read_text());assert rr['exit_status']==0 and rr['swaps']==0 and rr['source_unchanged'] and rr['lock_unchanged'] and rr['cgroup_swap_current']==0
 assert rr['limits']['memory.max']==str(2*2**30) and sha(d/'input.json')==rr['input_sha256']
 ad=json.loads((P/'extra'/(phase+'-admission.json')).read_text());assert ad['admitted'] and ad['root']=='/sys/fs/cgroup'
 assert ad['reserved_bytes']+ad['additional_bytes']+ad['uncapped_background_allowance_bytes']<ad['limit_bytes']
ad=json.loads((P/'claims_row_write_preserves_initialized_prefix-v6-admission.json').read_text());assert ad['admitted'] and ad['root']=='/sys/fs/cgroup'
assert ad['reserved_bytes']+ad['additional_bytes']+ad['uncapped_background_allowance_bytes']<ad['limit_bytes']
bind=json.loads((P/'extra/extraction-binding.json').read_text());assert bind['native_source_sha256']==sha(P/'proofs.rs') and bind['native_receipt_sha256']==sha(D/'receipt.json')
body=source[source.index('fn owned_step('):source.index('\nfn row(')];assert body==bind['owned_body']
expected=(P/'payload/r1_semantic.rs').read_text()+'\ntype Claims = [[QM31;29];3];\ntype Row = [QM31;29];\n'+body.replace('fn owned_step(', 'pub fn claims_owned_step(')+'\n'
assert (P/'extra/owned-reference.rs').read_text()==expected
for n in ['Types','Funs']:
 assert (P/'extracted'/(n+'.lean')).read_bytes()==(P/'extra/generated/AspisS1ClaimsOwnedStep'/(n+'.lean')).read_bytes()
subprocess.run(['python3',str(R/'tools/s1-claims-row-step-20261024/normalize.py'),'--check'],check=True)
m=json.loads((P/'lean-targets.json').read_text());imp=json.loads((E/'s1-claims-owned-step-import-pins.json').read_text())
for n,attempt in m['targets'].items():
 d=E/attempt;rr=json.loads((d/'receipt.json').read_text());assert rr['exit_status']==0 and rr['swaps']==0
 assert sha(S/(n+'.lean'))==sha(d/'source.lean')==rr['source_sha256']==imp['targets'][n]['source_sha256']
 if n!='S1ClaimsOwnedStepTypesV1':assert rr['print_axioms']
 for audit in rr['print_axioms']:
  matches=re.findall(r'\[(.*?)\]',audit,re.S)
  if matches:assert set(matches[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
tools=json.loads((P/'tools.json').read_text())
for group in ['files','rust','reused']:
 for rel,h in tools[group].items():assert sha(R/rel)==h,rel
print(json.dumps(dict(status='PASS',lean=m['metrics'],native_wall_seconds=r['wall_seconds'],native_peak_rss_bytes=r['peak_rss_kib']*1024,native_checks=769,native_covers=3,native_import_files=len(i['native_imports']),native_uninitializedness_proved=False,whole_claims_closed=False,scope=m['scope'])))
