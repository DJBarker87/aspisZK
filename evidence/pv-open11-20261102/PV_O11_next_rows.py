"""Fail-closed source-shape checks. These do not certify native correspondence."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def text(name):return (D/name).read_text()
def tokens(s):
 s=re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
 return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',s)
def body(s,anchor):
 a=s.index('{',s.index(anchor));n=0
 for i in range(a,len(s)):
  n+=(s[i]=='{')-(s[i]=='}')
  if n==0:return s[a:i+1]
 raise ValueError(anchor)
def eq(s,anchor,want):return tokens(body(s,anchor))==tokens(want)
def get(path):
 b=subprocess.check_output(['git','show','HEAD:'+path]);return b
pins=json.loads(text('PV_O11_adopted-source-pins.json'))
for path,x in pins.items():
 assert sha((D/x['snapshot']).read_bytes())==x['sha256']
 assert x['matches_adopted'] and x['sha256']==x['adopted_expected']
source=text('inputs/client/state_only_entropy.rs');diag=text('inputs/client/diagnostics.rs')
path=text('inputs/std-path.rs');string=text('inputs/alloc/string.rs');vec=text('inputs/alloc/vec.rs');raw=text('inputs/alloc/raw_vec.rs')
prover=text('inputs/client/prover.rs');checker=text('inputs/client/z9e.rs')
checks={
 'string_complete_body':eq(string,'pub fn with_capacity(capacity:', '{ String { vec: Vec::with_capacity(capacity) } }'),
 'vec_global_wrapper':eq(vec,'pub const fn with_capacity(capacity:', '{ Self::with_capacity_in(capacity, Global) }'),
 'literal69_actual_caller':tokens('let name = reservation_name(digest,String::with_capacity(69),0); self.directory.join(name)')==tokens(body(source,'fn reservation_path(')[body(source,'fn reservation_path(').index('let name ='):-1]),
 'one_application_string_capacity_site':len(re.findall(r'String::with_capacity\(',source))==1,
 'raw_layout_error_retained':'Err(_) => return Err(CapacityOverflow.into())' in body(raw,'fn try_allocate_in('),
 'raw_zero_layout_retained':'if layout.size() == 0' in body(raw,'fn try_allocate_in('),
 'raw_allocator_error_retained':'Err(_) => return Err(AllocError { layout, non_exhaustive: () }.into())' in body(raw,'fn try_allocate_in('),
 'native_join_clone_first':eq(path,'fn _join(&self, path:', '{ let mut buf = self.to_path_buf(); buf.push(path); buf }'),
 'native_join_generic_owned_parameter':eq(path,'pub fn join<P:', '{ self._join(path.as_ref()) }'),
 'native_clone_keeps_os_bytes':eq(path,'pub fn to_path_buf(&self)', '{ PathBuf::from(self.inner.to_os_string()) }'),
 'native_absolute_clears_after_clone':'if need_clear {\n            self.inner.truncate(0);' in body(path,'fn _push('),
 'global_allocator_null_aborts':all('if '+ptr+'.is_null() { std::process::abort(); }' in body(diag,anchor) for ptr,anchor in [('p','unsafe fn alloc('),('p','unsafe fn alloc_zeroed('),('q','unsafe fn realloc(')]),
 'global_allocator_no_cfg': '#[global_allocator]' in diag and '#[cfg' not in diag,
 'deployed_panic_abort':'panic = "abort"' in text('inputs/client/tool-Cargo.toml') and '--profile client' in text('inputs/client/build-client.sh'),
 'production_feature_selected':'aspis-r1-cost-probe/ct-host-prover' in text('inputs/client/build-client.sh'),
 'check_times_refs_exactly_three':len(re.findall(r'\bCHECK_TIMES\b',prover))==3,
 'check_times_declaration_gated':'#[cfg(not(feature="ct-host-prover"))] static CHECK_TIMES:' in prover,
 'check_times_take_gated':tokens(body(prover,'pub fn take_check_times()'))==tokens('{ #[cfg(not(feature="ct-host-prover"))] { CHECK_TIMES.with(|v| core::mem::take(&mut *v.borrow_mut())) } #[cfg(feature="ct-host-prover")] { Vec::new() } }'),
 'check_times_store_gated':'#[cfg(not(feature="ct-host-prover"))] CHECK_TIMES.with(|v| v.borrow_mut().push(times)); #[cfg(feature="ct-host-prover")] let _ = times;' in body(prover,'fn public_check('),
 'checker_call_is_retained':'let (accepted,times)=aspis_z4b_probe::p_r1_check(challenges);' in body(prover,'fn public_check('),
 'checker_four_clock_pairs_retained':body(checker,'pub fn p_r1_check(').count('Instant::now()')==4 and body(checker,'pub fn p_r1_check(').count('.elapsed().as_secs_f64()')==4,
 'checker_quiet_tls_retained': 'static QUIET: std::cell::Cell<bool>' in checker and body(checker,'pub fn p_r1_check(').count('QUIET.with(')==2 and 'ct-host-prover' not in checker,
 'no_custom_times_drop':'#[derive(Clone, Copy, Debug, Default)]\npub struct R1CheckTimes' in checker,
}
# Exact old consumer branch; retain source, never silently change the old theorem.
old=get('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDEAC_JoinHandlers.lean')
(D/'inputs/PV_RDEAC_JoinHandlers.lean.txt').write_bytes(old)
checks['historical_overflow_consumer_unwinds']='| .error .capacityOverflow => release free owned (release free e.buffer e.world)' in old.decode()
# Matched source controls: moving push before clone or retaining TLS writes fails.
checks['negative_join_order_rejected']=not eq(path,'fn _join(&self, path:', '{ let mut buf = PathBuf::new(); buf.push(path); buf }')
checks['negative_tls_live_branch_rejected']=tokens(body(prover,'pub fn take_check_times()'))!=tokens('{ CHECK_TIMES.with(|v| core::mem::take(&mut *v.borrow_mut())) }')
report={'classification':'script-checked source shapes and adopted-source identity; NOT complete native bindings, a release audit, or restored rows','checks':checks,'ok':all(checks.values()),'inputs':{str(p.relative_to(D)):sha(p.read_bytes()) for p in list((D/'inputs/client').glob('*'))+list((D/'inputs/alloc').glob('*'))+[D/'inputs/std-path.rs',D/'inputs/PV_RDEAC_JoinHandlers.lean.txt']},'rows':{
 'V181':{'status':'OPEN','exact_premise':'Instantiate the physical literal69 constructor/name-stage law with adopted native String/header/allocator/world and actual diagnostic/abort observation in the same caller frame; cover all reached source callers or prove exclusions. The adopted allocator aborts on null inside alloc, before std receives AllocError; bind that terminal prefix instead of assuming std OOM-handler return. No allocation-success assumption is needed.','direct_route':'N90505 Charon exit0 but has_errors=true: extractor rustc_trait_elaboration/src/item_ref.rs:312:27 range start index 1 out of range for slice of length 0 while extracting RawVecInner::try_allocate_in. Not accepted; never translate this LLBC.'},
 'V178':{'status':'OPEN','exact_premise':'Instantiate native clone-first Path::join with actual owned String argument/header and full allocator/world/observer frame. At adopted panic=abort, overflow invokes the constant panic hook then aborts WITHOUT either partial-buffer or owned-name Drop; do not install historical JoinHandlers.finalWorld overflow release/release. Preserve success owned-name release and all allocation-failure prefixes. Native diagnostics/exhaustive caller exclusions and coherent consumer replay remain.','direct_route':'Same RawVecInner allocator cone as N90505 is already known not extractable. No unchanged common-cone retry is launched.'},
 'V369':{'status':'OPEN','established_source_slice':'With ct-host-prover and cfg(test)=false, CHECK_TIMES declaration/write/read are absent; take_check_times returns Vec::new. R1CheckTimes is Copy. These exact selected-source bodies match the adopted bundle input manifest.','exact_premise':'Bind this selected-source slice and the retained p_r1_check call, four Instant/elapsed pairs, QUIET TLS set/reset/hook lookup, resource failure and ordered events to the existing L2 SAME-cp source/observer law at the adopted binary. CHECK_TIMES gating alone does not remove native timing/TLS work or prove the joint law.'}}}
(D/'PV_O11_next-rows.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'ok':report['ok'],'checks':len(checks),'failed':[k for k,v in checks.items() if not v],'restored':0}));assert report['ok']
