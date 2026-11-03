"""Bind the reached constructor sites/public initial sizes to adopted source."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evhB-20261103');sha=lambda b:hashlib.sha256(b).hexdigest()
adopted=json.load(open('evidence/pv-evh10-20261102/adopted-backend-confirmation.json'))
rev=adopted['adopted_build_receipt']['revision']
def read(r,p):return subprocess.check_output(['git','show',r+':'+p])
def body(s,anchor):
 a=s.index(anchor);i=s.index('{',a);j=i+1;n=1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
prover='crates/aspis-r1-cost-probe/src/prover.rs';hiding='crates/aspis-prover/src/state_only_hiding.rs'
rows=[]
for module,path,anchor,need in [
 ('MaterialFromEntropy',hiding,'pub(crate) fn build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref(',['StateOnlyMaskBuildError::Layout']),
 ('ApplyMaterial',hiding,'pub fn apply_pool_v1_pair_forest_mask_material_v1(',['StateOnlyMaskBuildError::Layout']),
 ('PrivateSalts',prover,'fn derive_private_salts(',['salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT).map_err(|_|Error::Allocation)?','result.map(PrivateSalts::new)']),
 ('PrepareOpening',prover,'fn prepare_opening(',['.map_err(|_|Error::Allocation)?']),
 ('PublishCompact',prover,'fn publish_compact(',['Vec::with_capacity(compact::PROOF_BYTES)','.map_err(|_|Error::Semantic)?']),
 ('PrivateSaltStep',prover,'fn derive_private_salt_step(',['.map_err(|_|Error::Semantic)?','salts.push(salt)'])]:
 current=read('HEAD',path);old=read(rev,path);b=body(current.decode(),anchor);assert b==body(old.decode(),anchor)
 for item in need:assert item in b,(module,item)
 lean=Path('lean/PV_EVHB_'+module+'.lean').read_bytes()
 sites=re.findall(r'PV_EVHB_CallbackEffects.mapErr c.drop_OPEN c.drop_OPEN ([\w.]+)',lean.decode())
 assert len(sites)==(2 if module=='PublishCompact' else 1),(module,sites)
 rows.append(dict(module='PV_EVHB_'+module,path=path,anchor=anchor,adopted_revision=rev,source_body=b,body_sha256=sha(b.encode()),file_sha256=sha(current),adopted_file_sha256=sha(old),lean_sha256=sha(lean),constructor_sites=sites))
# The actual extraction and its complete mutable restoration carrier are pinned.
prep=json.load(open(E/'prepare-PV_EVHB_CallbackSelection.json'))['result']
pin=next(v['source'] for v in prep['project_checks'] if v['module']=='R1Z.ProverRwFullFuns')
funs=read(pin['revision'],pin['path']);assert sha(funs)==pin['source_sha256']
assert b'let (r, salts)' in funs and b'alloc.vec.Vec.try_reserve_exact Global' in funs
extra=[]
for path,anchor,need in [
 ('crates/aspis-r1-cost-probe/src/host_work.rs','pub(crate) fn map<',['Vec::with_capacity(b-a)','Vec::with_capacity(n)']),
 ('docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','pub fn range(',['n / THREADS','n % THREADS']),
 ('crates/aspis-r1-cost-probe/src/host_commitment.rs','pub fn new(values: Vec<[u8; 32]>)',['Self(values)'])]:
 raw=read('HEAD',path);old=read(rev,path);b=body(raw.decode(),anchor);assert b==body(old.decode(),anchor)
 for item in need:assert item in b,(path,item)
 extra.append(dict(path=path,anchor=anchor,adopted_revision=rev,body=b,body_sha256=sha(b.encode()),file_sha256=sha(raw)))
# Counts derive from public constants in the actual call sites, not an arbitrary
# promise of equal witness-dependent sizes. Later append/growth is NOT discharged.
out=dict(evidence_class='own-1 structural reached constructor-site/public-prefix binding; Lean source equations checked separately',
 extraction=pin,source=rows,additional_source=extra,public_initial_requests=[
 dict(site='derive_private_salts',count='aspis_core::r0::FIBRE_COUNT',empty_buffer=True,element='[u8;32]',byte_size='FIBRE_COUNT * size_of::<[u8;32]>()',proof='PV_EVHB_SaltsReserve.selected_prefix / initial_size'),
 dict(site='publish_compact',count='compact::PROOF_BYTES',empty_buffer=True,element='u8',byte_size='PROOF_BYTES * size_of::<u8>()',proof='PV_EVHB_PublishInstall.install_view; native layout association remains OPEN')],
 retained=[
 'V183 SUSPENDED(K-3) per runjoin73 handoff: these Lean laws do not reinstate the Kani source credit.',
 'V370 compiler-cohort: source-to-machine preservation, capture layout, moves, drop glue and panic=abort interpretation.',
 'HEAP-ENTRY/rdea-1: native metadata/address/capacity, layout/padding, Global/System answer validity, same physical memory and observation encoding association.',
 'V400: initial allocator state/world answers witness-independent; equality of public metadata is a hypothesis of public_metadata, not inferred.',
 'V400/rdea-2: op257/host_work.map thread/TLS initialization, joins, worker panic/exhaustion occurrence and timing need an advancing stateful WORLD source association. Shared public ranges do not establish this.',
 'Later Vec push/extend/append growth, owned Vec/Box/drop and full prover entry event adequacy remain OPEN.',
 'WorkerRequests is a source-indexed list of potential explicit capacities. It is not the temporal arrival order or a complete trace under callback panic/divergence; native scheduling/failure timing and std::thread/TLS/collect allocation remain V400.',
 'PrivateSaltsNew installs typed new/move effects supplied by new_OPEN. Its actual physical move/drop/native observation association remains V370/L3; no PrivateSalts destructor zeroization is inferred.',
 'Native diagnostic/hook/backtrace and unwind/abort effects remain in supplied effectful drops/leaves; no silence or infallibility assumed.',
 'D520/U/D524 and V221/V222/L1/L2/L3 obligations remain; no endpoint/deployment row removed; T unchanged.'
 ],rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0)
p=E/'source-binding.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS adopted callback sites and public initial request binding; native adequacy retained')
