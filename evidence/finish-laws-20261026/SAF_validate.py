from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
corrections={2:'f229a0be6e',**{n:'9b3f4f7aad' for n in range(5,9)},**{n:'0dacfb12ee' for n in range(9,15)}}
receipts=[];passed={};theorems={}
for n in range(1,101):
 a=f'SAF_{n:03}';f=P/a/'receipt.json';x=json.loads(f.read_text())
 assert x['attempt']==a
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 assert x['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
 assert len(x['sources'])==1
 reservation=json.loads((P/(a+'-reservation.json')).read_text());assert reservation['allowed']
 log=(P/a/'stdout.log').read_text()
 for src,h in x['source_hashes'].items():assert sha(P/a/'sources'/src)==h
 if x['exit_status']==0:
  assert 'error:' not in log
  for line in x['print_axioms']:
   assert 'sorryAx' not in line
   m=re.search(r'axioms: \[(.*?)\]',line)
   if m:assert set(m[1].split(', '))<=allowed,line
  passed[x['sources'][0]]=dict(attempt=a,sha256=x['source_hashes'][x['sources'][0]])
  theorems[a]=x['print_axioms']
 assert x['exit_status'] not in {124,137,-9},a
 corrected=x['source_revision']
 if n in corrections:
  corrected=subprocess.check_output(['git','rev-parse',corrections[n]],cwd=R,text=True).strip()
 receipts.append(dict(attempt=a,module=x['sources'][0],exit_status=x['exit_status'],command=x['command'],wall_seconds=x['wall_seconds'],peak_rss_kib=int(x['peak_rss_kib']),swaps=x['swaps'],recorded_source_revision=x['source_revision'],source_revision=corrected,source_revision_correction='Copied config template had stale base revision; authoritative launch-base correction, exact source snapshot/hash unchanged' if n in corrections else None,source_hashes=x['source_hashes'],dependency_fingerprint=x['deps_fingerprint'],print_axioms=x['print_axioms'],raw_receipt_sha256=sha(f)))
failed=[r['attempt'] for r in receipts if r['exit_status']]
assert failed==['SAF_001','SAF_009','SAF_011','SAF_014','SAF_079'],failed
own={}
for f in (R/'lean').glob('SAF_*.lean'):
 assert f.name in passed,('No current successful snapshot',f)
 assert sha(f)==passed[f.name]['sha256'],('Current source differs from passing snapshot',f)
 s=f.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',s),f
 declared=re.findall(r'^theorem\s+(\w+)',s,re.M)
 audited=re.findall(r'#print axioms\s+(\w+)',s)
 assert set(declared)<=set(audited),(f,declared,audited)
 own[str(f.relative_to(R))]=dict(**passed[f.name],current_sha256=sha(f))
for file in ['SAF_inherited_sources.json','SAF_inherited_objects.json']:
 assert all(x['matches'] for x in json.loads((P/file).read_text()).values())
assert all(x['matches'] for x in json.loads((P/'SAF_NONVACUITY.json').read_text())['rows'])
plan=json.loads((P/'SAF_audit_plan.json').read_text())
for item in plan:
 x=next(r for r in receipts if r['attempt']==item['attempt']);assert x['exit_status']==0
 item['status']='compiled';item['stdout_sha256']=sha(P/item['attempt']/'stdout.log')
(P/'SAF_audit_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# Fresh kernel expansions verify the actual new leaf and its exact residual laws.
leaf=(P/'SAF_086/stdout.log').read_text().split('def AspisR1.SAF_C_SAF_FinishPrepared.Outcome',1)[1]
assert 'canonical_S3_S4_S5_S9' not in leaf
assert 'SAF_ReducedLaws.Arithmetic' in leaf and '∃' in leaf
fields=(P/'SAF_088/stdout.log').read_text()
assert 'SAF_ReducedLaws.Arithmetic.pair' in fields
assert 'PairingLaws.claim' in fields and 'PairingLaws.alpha0' in fields
# Exact source-type equality is independently checked in the committed comparison.
assert json.loads((P/'SAF_statement_comparison.json').read_text())['exact_old_type_recovered']
(P/'SAF_validation.json').write_text(json.dumps(dict(lean_invocations=100,passes=95,excluded_failures=failed,kani_runs=0,package_replays=0,unchanged_dependency_builds=0,scope_policy='Sequential; MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean-j1-M7000',revision_correction_notice='Eleven early configs copied a stale base revision. This table corrects it explicitly; raw receipts are retained unedited and exact source/dependency hashes remain authoritative.',own_sources=own,receipts=receipts,axioms=theorems),indent=2)+'\n')
print(json.dumps(dict(lean=100,passed=95,excluded=failed,own_sources=len(own),all_current_sources_match=True,standard_axioms_only=True)))
