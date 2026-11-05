"""Reconstruct immutable whole-body Bool contracts; never replay passing shapes."""
from pathlib import Path
import subprocess,json,hashlib,tempfile,re
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='evidence/native-u04d-20261028/';pins={}
def get(p,rev='HEAD'):
 b=subprocess.check_output(['git','show',rev+':'+p],cwd=R);pins[rev+':'+p]=hashlib.sha256(b).hexdigest();return b
sha=lambda b:hashlib.sha256(b).hexdigest()
path='crates/aspis-statement/src/pool_v1/verifier_registry.rs';frozen=get(path,F)
patch=get('evidence/native-u04c-20261028/NCC_getter_annotations.patch')
with tempfile.TemporaryDirectory(prefix='NIJ_active_') as tmp:
 t=Path(tmp)/path;t.parent.mkdir(parents=True);t.write_bytes(frozen)
 subprocess.run(['git','apply','--unsafe-paths','-'],input=patch,cwd=tmp,check=True)
 annotated=t.read_bytes()
for m in ['NBX_slots','NCC_slots','NCF_slots']:annotated+=f'\n#[cfg(kani)]\n#[path = "{m}.rs"]\nmod {m};\n'.encode()
harness=get(P+'NCF_stage1_source.rs.txt');gate=get(P+'NCF_gate.py','0aa48e0ad2b');rows=[]
for a,positive in [('NCF_K002',True),('NCF_K003',False),('NCF_K006',True),('NCF_K007',False)]:
 rc=json.loads(get(P+a+'/receipt.json'));g=json.loads(get(P+a+'-graph.json'));log=get(P+a+'/stdout.log').decode()
 for suffix,data in [('/verifier_registry.rs',annotated),('/NCF_slots.rs',harness),('NCF_gate.py',gate),('NCC_getter_annotations.patch',patch)]:
  h=[v for k,v in rc['source_hashes'].items() if k.endswith(suffix)];assert len(h)==1 and h[0]==sha(data),(a,suffix)
 assert g['graph_matches_frozen'] and g['offline'] and g['lock_unchanged']
 assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert rc['limits']==dict(**{'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'})
 assert (rc['exit_status']==0)==positive and g['kani_exit']==rc['exit_status'] and rc['swaps']=='0'
 assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in log
 if not positive:assert '1 of ' in log and 'failed' in log and '*result !=' in log
 name=rc['module'].split('::')[-1];body=re.search(r'fn '+name+r'\(\)\{([^}]+)\}',harness.decode()).group(1)
 assert 'kani::any()' in body and 'stub' not in body
 rows.append(dict(attempt=a,positive=positive,receipt_sha256=pins['HEAD:'+P+a+'/receipt.json'],graph_sha256=pins['HEAD:'+P+a+'-graph.json'],harness=name,body=body,wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib']))
# Exact reachable source: no conditional compilation on types, methods or constants.
s=frozen.decode().split('#[cfg(test)]')[0];assert '#[cfg(' not in s and '#[cfg_attr(' not in s
for v in ['V1','V2']:
 region=s.split('impl VerifierRegistryEntry'+v+' {',1)[1].split('\n}',1)[0]
 active=region.split('pub fn is_active_at',1)[1];assert 'self.has_no_retirement_slot() || slot < self.retirement_slot' in active
 assert 'self.status == VerifierEntryStatusV1::Active' in active and 'self.activation_slot <= slot' in active
 assert 'self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT' in region
 assert 'POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT: u64 = u64::MAX' in s
for token in ['cfg-if','libc','copy_from_slice','clone_from_slice','copy_nonoverlapping','to_vec','Vec<','Option<fn','dyn ']:assert token not in active,token
model=get('lean/NDO_NBX_SlotValues.lean').decode();proof=get('lean/NCF_EntryContract.lean').decode();own=(E/'NIJ_ActiveSlots.lean').read_text()
for n in ['activeStatus','active','op29','op30']:
 orig=re.search(r'def '+n+r'\b.*?(?=\n(?:def |/\*\*|/--|end |theorem ))',model,re.S).group(0).strip()
 assert orig in own,n
focused=json.loads((E/'NIJ_L047/receipt.json').read_text());assert focused['exit_status']==0 and sha(own.encode()) in focused['source_hashes'].values()
assert all('sorryAx' not in a for a in focused['print_axioms'])
out=dict(status='PASS',frozen_revision=F,pins=pins,receipts=rows,annotated_source_sha256=sha(annotated),frozen_source_sha256=sha(frozen),feature_parity='Historical runs default statement features. Reached typed records/status/constants/inherent methods have no cfg; same actual frozen source across deployed features. Only Bool/integer comparisons and actual no-retirement helper, no feature-dependent dependency or cfg-if/libc reached. No new deployed run claimed.',domain='All four status constructors, every typed record field arbitrary, every u64 slot; shared receiver, no requires beyond true. Pure Bool interface; no stub_verified selected. Matched inverse-ensures controls for both.',copy='Exact KMX patch present for all four; result reaches no copy primitive. Same-configuration inverse assertions fail.',callee_laws='V1 uses CLOSED NHY retirement_v1 only; V2 uses CLOSED NHY retirement_v2 only; opposite typed receiver excluded. NIJ_ActiveSlots.retirement_v1/v2 prove source call structure and full domains.',lean='NIJ_L047',credit='NONE: source association is insufficient; unchanged NFK rejects historical NCF positives suspended by K-3 static-token review. Rows194/196 remain OPEN. See NIJ_ACTIVE_REJECTED.json.')
(E/'NIJ_ACTIVE_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n');print('PASS active source association')
