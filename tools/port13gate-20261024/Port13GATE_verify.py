from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/port13gate-20261024';T=R/'tools/port13gate-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(T/'Port13GATE_auth_gen.py'),'--check'],check=True)
subprocess.run([sys.executable,str(T/'Port13GATE_admission_test.py')],check=True)
configs=sorted(T.glob('lean-*.json'));assert len(configs)<=6
attempts=[];final={};actual=0
for p in configs:
 c=json.loads(p.read_text());a=c['attempt'];receipt=E/a/'receipt.json';admission=E/(a+'-reservation.json')
 row={'attempt':a,'configuration_sha256':sha(p)}
 if admission.exists():
  ad=json.loads(admission.read_text());assert ad['admitted'] and ad['reserved_bytes']+ad['additional_bytes']<55*1024**3
  capped=[g for g in ad['all_cgroups'] if 'reservation_bytes' in g]
  for parent in capped:
   assert all(not child['path'].startswith(parent['path']+'/') for child in capped if child!=parent)
  row.update({'admission_sha256':sha(admission),'admission_reserved_bytes':ad['reserved_bytes']})
 if receipt.exists():
  x=json.loads(receipt.read_text());actual+=1
  assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert x['swaps']=='0'
  row.update({k:x[k] for k in ['command','source_revision','source_tree_dirty','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
  row['receipt_sha256']=sha(receipt)
  if x['exit_status']==0:
   assert x['print_axioms']
   for line in x['print_axioms']:
    axioms=line.split('depends on axioms: [',1)[1].rstrip(']')
    names={re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in axioms.split(',')}
    assert names<={'propext','Classical.choice','Quot.sound'},line
   for f,h in x['source_hashes'].items():
    if sha(L/f)==h:final[f]={'sha256':h,'attempt':a}
  else:row['failure_assessment']='Audit-only unsupported pp.width; removed in changed audit lean-004. No resource failure.'
 else:row['status']='pre-Lean reservation charged; no compile receipt'
 attempts.append(row)
for p in L.glob('Port13GATE_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',s)
 assert p.name in final,p
assert '⋯' not in (E/final['Port13GATE_Audit.lean']['attempt']/'stdout.log').read_text()
before=(E/'Port11PROV_accepted-statement.lean.txt').read_text();after=(E/'Port13GATE_accepted-statement.lean.txt').read_text()
assert before[before.index('    (sourceAccepted'):]==after[after.index('    (sourceAccepted'):]
assert 'p6 :' not in after and '(binary :' not in after
assert 'native D H' in after
prior=R/'evidence/port12count-20261024/manifest.json'
provenance={p.name:sha(p) for p in T.glob('*.py')}
x={'schema':'focused-extractor-proof-packet-v1','status':'Concrete indexed authentication without native totality; both deployed targets not yet established',
 'base':'fa9956130a','revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'inherited_actual_lean_compiles':213,'inherited_pre_lean_charges':1,'inherited_charged':214,
 'new_reserved_attempts':len(configs),'new_actual_lean_compiles':actual,'actual_lean_compile_tally':213+actual,
 'pre_lean_charges':1+len(configs)-actual,'conservative_charged_tally':214+len(configs),
 'remaining_conservative_slots':6-len(configs),'lean_limit':220,'kani_runs':0,'kani_limit':20,
 'prior_ledger':{'path':str(prior.relative_to(R)),'sha256':sha(prior)},'tools_sha256':provenance,
 'final_sources':final,'attempts':attempts,'full_manifest_replay':False,'artifact_identity_gate':'none; unchanged source cached evidence reused only'}
(E/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['actual_lean_compile_tally','pre_lean_charges','conservative_charged_tally','remaining_conservative_slots']}))
