"""Validate final raw proofs/fixtures/scan and record exact source/resource fields."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda n:json.loads((E/n).read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
raw=load('NHL_audit/batch0/proof0.json');fixtures=load('NHL_audit/fixtures/fixtures.json')
manifest=load('NHL_AUDIT_ROOTS.json')['groups'][0]
assert raw['exit_status']==fixtures['exit_status']==0
assert sorted(r['root'] for r in raw['results'])==sorted(manifest)
assert all(r['equal'] and r['collect_axioms']==r['walked_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw['results'])
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert len(fixtures['results'])==8
assert all(r['equal'] and r['walked_axioms']==expected[r['root']] and r['collect_axioms']==expected[r['root']] for r in fixtures['results'])
pins=[];forbidden=[]
for tag,rows in [('proof0',raw['results']),('fixtures',fixtures['results'])]:
 for row in rows:
  name='NHL_NEP_'+tag+'_'+row['root']+'_REACHABLE.txt';p=E/(name+'.xz');b=lzma.decompress(p.read_bytes())
  assert sha(b)==(E/(name+'.sha256')).read_text().strip()
  if b'XRn_Join' in b:forbidden.append(row['root'])
  pins.append(dict(root=row['root'],path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),raw_sha256=sha(b),raw_bytes=len(b)))
assert not forbidden,forbidden
(E/'NHL_RAW_AUDIT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
scan=[json.loads(l) for l in (E/'NHL_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in scan)
walker=R/'evidence/axaudit2-20261102/NEP_WALKER.lean'
assert walker.read_bytes()==(E/'NHL_WALKER_SOURCE.lean.txt').read_bytes()
reference=(R/'evidence/axaudit2-20261102/NEP_Driver.lean').read_text();driver=(E/'NHL_ProofDriver.lean').read_text()
# The complete import/environment/kernel-walker action is unchanged.
assert reference[reference.index('  let env ←'):]==driver[driver.index('  let env ←'):]
assert 'namespace NER' not in driver
binary=load('NHL_L069/NHL_ProofDriver_BINARY_PIN.json');assert binary==load('NHL_L070/NHL_ProofDriver_BINARY_PIN.json')
rows=[json.loads(l) for l in (E/'NHL_ATTEMPTS.jsonl').read_text().splitlines()]
assert sum(r['kind']=='kani' for r in rows)==0 and sum(r['kind']=='extract' for r in rows)==2
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rows:
 full=load(r['full_receipt']);assert full['limits']==limits and str(full['swaps'])=='0'
 ad=load(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
 if r['kind']=='lean':assert '-M7000' in full['command']
assert len([r for r in rows if r['attempt'].startswith('NHL_L')])<=80
for target in ['prepare','tx1']:
 p=load('NHL_emitted/'+target+'/NHL_EXTRACTION_PINS.json');assert p['exit']==p['charon_exit']==0 and p['lock_before']==p['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert load('NHL_LEDGER_DELTA.json')['promotions']==[]
a=dict(status='PASS_CONDITIONAL_MODEL_SIDE_AX2',native_or_composed_promotions=0,root_count=len(raw['results']),roots=raw['results'],fixtures=fixtures['results'],walker_unchanged=True,walker_sha256=sha(walker.read_bytes()),driver_core_byte_identical_to_NEP=True,driver_diff='NHL_DRIVER_VS_NEP.diff',same_final_binary_for_fixtures_and_roots=binary,standard_axioms_only=True,raw_equals_collect=True,no_XRn_Join=True,scan=dict(exit=0,modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),cached_replicas=sum(len(r.get('cached_replicas',[])) for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0),selected_attempts=['NHL_E001','NHL_E002','NHL_L058','NHL_L059','NHL_L066','NHL_L067','NHL_L068','NHL_L069','NHL_L070','NHL_L071'],excluded_initial_audit='NHL_L065 (unused inherited driver helpers; replaced by minimal NEP adaptation)',scan_reuse='L066 model closure unchanged: proof driver is not imported by NHL_COMBINED_IMPORT; no unchanged scan replay',budget=dict(kani_used=0,kani_max=0,lean_support_used=sum(r['attempt'].startswith('NHL_L') for r in rows),lean_support_max=80,extraction_used=2,extraction_max=2),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',headline='AspisR1.RPx_Deployed.deployed',trust_changes=[],abi_compiler_runtime_and_native_transport_retained=True)
a['selected_receipts']=[{k:r[k] for k in ['attempt','module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','print_axioms']} for n in a['selected_attempts'] for r in [load(n+'/receipt.json')]]
a['all_attempt_metrics']=dict(wall_seconds_sum=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,submitted_scopes=len(rows))
(E/'NHL_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
print(json.dumps({k:a[k] for k in ['status','root_count','scan','budget','all_attempt_metrics']}))
