"""Source association checks only. No compiler, solver, or source mutation."""
from pathlib import Path
import re,json,hashlib,lzma,base64,subprocess
E=Path(__file__).resolve().parent;P=E/'caller'
sha=lambda b:hashlib.sha256(b).hexdigest()
def tokens(t):
 t=re.sub(r'//[^\n]*|/\*.*?\*/','',t,flags=re.S)
 return re.findall(r'::|->|=>|\w+|[^\s]',t)
def block(t,n):
 a=t.index('fn '+n+'(');a=t.rfind('\n',0,a)+1;s=t.index('{',a);d=1;i=s
 while d:i+=1;d+=(t[i]=='{')-(t[i]=='}')
 return t[a:i+1]
results={}
for n in ['host','reference']:
 frozen=(E/(n+'.frozen.rs')).read_text();selected=(P/(n+'.rs')).read_text()
 assert block(frozen,'sum_high')==block(selected,'sum_high')
 assert block(frozen,'sum')==block(selected,'sum')
 results[n+'_sum_full_bodies_exact']=True
h=block((E/'host.frozen.rs').read_text(),'sum_high')
c=block((P/'context.rs').read_text(),'sum_high').replace('pub fn','fn',1).replace(',log:&mut Log','').replace('sum=add(sum,selectors.high[block],log);','sum=sum.add(selectors.high[block]);')
assert tokens(h)==tokens(c),(h,c)
results['context_caller_erasure_exact']=True
assert 'pub high:[QM31;64],pub low:[QM31;16]' in (P/'context.rs').read_text()
assert '.mul(' not in h and '.square(' not in h
results['sum_old_mul_square_stubs_unreached']=True
array=(P/'array.rs').read_text();frozen=(E/'array.frozen.rs').read_text()
assert frozen.split('\n')[1]==array.split('\n')[1]
assert 'struct Token;' in array and 'impl Drop for Token' in array
assert 'panic!("unexpected Token::drop: empty child domain")' in array
assert array.count('Vec::new()')==2 and array.count('array_from_vec::<Token,')==2
results['C051_zero_sized_noncopy_drop_carrier_retained']=True
# Recompute the exact local-state relocation, including its full raw output generator.
old=(E/'memo.frozen.rs').read_text();a=old.index('pub fn mul');old=old[a:]
old=old.replace('pub fn mul(a:QM31,b:QM31)->QM31 {eval(0,a,b)}','pub fn mul(a:QM31,b:QM31,log:&mut Memo)->QM31 {eval(0,a,b,log)}').replace('pub fn square(a:QM31)->QM31 {eval(1,a,a)}','pub fn square(a:QM31,log:&mut Memo)->QM31 {eval(1,a,a,log)}').replace('fn eval(tag:u8,a:QM31,b:QM31)->QM31 {unsafe {','fn eval(tag:u8,a:QM31,b:QM31,log:&mut Memo)->QM31 {{').replace('pub fn roundtrip16() {unsafe {','pub fn roundtrip16(log:&mut Memo) {{').replace('super::equivalence16::q()','super::q()').replace('mul(QM31::ONE,QM31::ZERO)','mul(QM31::ONE,QM31::ZERO,log)')
for n in ['USED','TAG','LEFT','RIGHT','OUTPUT']:old=re.sub(r'\b'+n+r'\b','log.'+n.lower(),old)
assert (P/'shared_callee16.rs').read_text().endswith(old)
results['memo_relocation_exact']=True
repeat=(P/'repeat_context.rs').read_text()
assert repeat.count('=mul(a,b,&mut log)')==2
assert 'assert_eq!(first,second)' not in repeat
assert 'let reply=q();' in repeat and 'kani::assume' not in repeat
results['repeat_independent_full_replies_no_equality_assumption']=True
payload=json.loads(lzma.decompress((E/'default-source.json.xz').read_bytes()))
w=base64.b64decode(payload['native/digest-0.10.7/src/core_api/wrapper.rs']).decode()
start=w.index('    /// K-3 local context:');end=w.index('    /// Create new wrapper',start)
assert w[:start]+w[end:]==(E/'wrapper.frozen.rs').read_text()
assert sha((E/'wrapper.frozen.rs').read_bytes())==json.loads((E/'V237-proof-association.json').read_text())['unchanged_constructor_binding']['sources']['digest-0.10.7/src/core_api/wrapper.rs']['sha256']
method=w[start:end];assert 'Self { core: oracle(), buffer: Default::default() }' in method
assert 'Self(unsafe {DEFAULT_STATE})' in (E/'default.frozen.rs').read_text()
assert 'unsafe {DEFAULT_STATE=state;}' in (E/'default.frozen.rs').read_text()
results['C053_original_derived_fields_and_read_projection_associated']=True
# Ensure every compiled harness/stub/oracle source has no static token; include!
# is resolved to the committed array.rs, and the KMX file is copied byte-exact.
for p in P.glob('*.rs'):
 assert not re.search(r'\bstatic\b',p.read_text()),p
results['compiled_harness_stub_oracle_no_static_tokens']=True
old_payload=json.loads(lzma.decompress((E.parent/'pv-k3scan-20261101/B3-source.json.xz').read_bytes()))
assert (P/'KMX_stubs.rs').read_bytes()==base64.b64decode(old_payload['tools/pv-b3p6-20261028/kmx/KMX_stubs.rs'])
results['KMX_exact_original']=True
# Negative source mutations must be rejected by the identity predicates too.
assert tokens(h)!=tokens(c.replace('selectors.high[block]','selectors.low[0]'))
assert (w[:start]+w[end:]).replace('core: T,','core: u32,')!=(E/'wrapper.frozen.rs').read_text()
results['source_mutation_controls_rejected']=2
results['scope']='source-structural associations, not a new kernel theorem or full native/world release'
results['C156_remaining']='Independent-reply G and memo relocation do not supply an actual full-raw ct-host-prover QM31::mul child bridge and its G/model substitution. The surveyed NEI release full products require canonical coordinates; do not narrow original raw inputs.'
(E/'ASSOCIATION.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
