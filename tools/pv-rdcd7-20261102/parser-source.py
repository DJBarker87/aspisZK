"""Owned structural parser route only; no extractor/Kani rerun."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';P=R/'evidence/pv-rdcd4-20261029'
lib={x['relative']:x for f in ['library-sources.json','v220-library-sources.json','v197-library-sources.json'] for x in json.load(open(P/f))}
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tok(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def span(s,context,marker):
 assert s.count(context)==1,(context,s.count(context));a=s.index(marker,s.index(context));b=s.index('{',a);d=0
 for m in lex.finditer(s,b):
  if m[0]=='{':d+=1
  elif m[0]=='}':
   d-=1
   if not d:return s[a:m.end()]
 raise AssertionError(marker)
field=subprocess.check_output(['git','show','HEAD:crates/aspis-core/src/field.rs'],cwd=R,text=True)
apps=[]
for context,expected,model,steps in [
('pub fn from_le_bytes(bytes: [u8; 4])','pub fn from_le_bytes(bytes:[u8;4])->Option<M31>{let v=u32::from_le_bytes(bytes);if v>=P{None}else{Some(M31(v))}}','BytesSource.scalar/scalar_binding','Decode all four bytes, compare raw representative with P, return None or exact unreduced value.'),
('pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31>','pub fn from_le_bytes(bytes:&[u8])->Option<CM31>{let a_bytes=match bytes[0..4].try_into(){Ok(value)=>value,Err(_)=>return None,};let a=M31::from_le_bytes(a_bytes)?;let b_bytes=match bytes[4..8].try_into(){Ok(value)=>value,Err(_)=>return None,};let b=M31::from_le_bytes(b_bytes)?;Some(CM31{a,b})}','BytesSource.component/cm','Checked first range, TryFrom array4 and scalar decode; None short circuit before second range; repeat and construct moved scalar fields.'),
('pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31>','pub fn from_le_bytes(bytes:&[u8])->Option<QM31>{let c0=CM31::from_le_bytes(&bytes[0..8])?;let c1=CM31::from_le_bytes(&bytes[8..16])?;Some(QM31{c0,c1})}','BytesSource.qm; PV_RDCD5_V197.source_reference/frame; actual callback association still required','Take first8 before parsing c0; None returns without second-half range. Only successful c0 evaluates8..16 and c1. Returned QM31 contains no reference.')]:
 body=span(field,context,'pub fn from_le_bytes(');assert tok(body)==tok(expected),context
 apps.append(dict(context=context,body=body,expected=expected,body_sha256=hashlib.sha256(body.encode()).hexdigest(),model='R1Z.PV_RDCD5_'+model if model.startswith('V197') else ('R1Z.PV_RDCD5_'+model if model.startswith('ParserRange') else 'R1Z.PV_RDCD4_'+model),source_steps=steps))
checks=[
('slice/index.rs','SliceIndex<[T]> for ops::Range<usize>','fn index(', 'Checked stop-start and stop<=length; success forms same readonly range via offset+length; failure calls slice_index_fail, hence panic (not arrayOutOfBounds); ParserRange.binding proves exact error constructor transport to the existing callback. Fixed parser bounds are ordered.','ParserRange.binding/success/oversized; SliceRange194.length; ParserWindows.compose/no_write'),
('array/mod.rs','const TryFrom<&[T]> for [T; N]','fn try_from(', 'Forward to borrowed-array conversion, then copied; concrete u8 Copy, no Clone callback. Root Err maps to original None.','TryArray194.into/backing/roundtrip'),
('array/mod.rs',"const TryFrom<&'a [T]> for &'a [T; N]",'fn try_from(', 'as_array length check; None becomes zero-sized TryFromSliceError; same backing array reference on success.','TryArray194.success/mismatch/backing'),
('slice/mod.rs','pub const fn as_array<','pub const fn as_array<','Check slice length=N, cast same pointer to arrayN, borrow it; otherwise None. No write or allocation.','TryArray194.backing; ParserWindows.no_write; pointer primitives at V370'),
('result.rs','impl<T, E> Result<&T, E>','pub const fn copied(self)','Copy the entire array value in Ok; move unchanged Err. Concrete [u8;4] has no Drop; no reference escapes the parser result.','TryArray194.into; complete caller None conversion'),
('option.rs','pub const fn ok_or<','pub const fn ok_or<','Some value becomes Ok, None becomes supplied zero-sized error; no arbitrary closure or allocation.','TryArray194.into; source CM match preserves Err=>None'),
('num/uint_macros.rs','pub const fn from_le_bytes','pub const fn from_le_bytes','Native-word read then from_le; u32 size4.','Endian194.binding; imported core.num.U32.from_le_bytes'),
('num/uint_macros.rs','pub const fn from_ne_bytes','pub const fn from_ne_bytes','Transmute exactly four bytes to u32; existing integer-layout/compiler primitive V370 retained.','Endian194.word/binding'),
('num/uint_macros.rs','pub const fn from_le(x: Self)','pub const fn from_le(x: Self)','Recorded x86_64 Linux target is little endian: return same word, other cfg branch not selected.','Endian194.binding')]
rows=[]
for path,ctx,marker,steps,model in checks:
 body=span(lib[path]['text'],ctx,marker)
 rows.append(dict(path=lib[path]['path'],file_sha256=lib[path]['sha256'],body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),source_steps=steps,model='R1Z.PV_RDCD5_'+model if model.startswith('V197') else ('R1Z.PV_RDCD5_'+model if model.startswith('ParserRange') else 'R1Z.PV_RDCD4_'+model)))
out=dict(row='V197',status='STRUCTURAL ARGUMENT: source snapshots and corrected model order/error branches checked; kernel and final-cohort gates still required',application_file='crates/aspis-core/src/field.rs',application_sha256=hashlib.sha256(field.encode()).hexdigest(),application_bindings=apps,library_bindings=rows,route='k-prime/own-1 exact owned Lean source reference. Pinned Aeneas escaping-reference loan-validation rejection remains recorded; no modified Rust, new extractor, Kani or loan-validation waiver.',before='Complete concrete parser source-to-reference Result law unbound at original arbitrary byte-slice input.',after_target='Same input, Option<QM31>, indexing-failure and short-circuit behavior; second-half bounds check stays after c0 None. Immutable input frame preserved, no returned borrow.',primitive_boundary='Typed pointer/read-only array4 copy and integer-layout/compiler semantics V370/D381/D386 retained. Native panic/observer/world obligations remain outside original Result abstraction.',pending='Corrected owned model, complete arbitrary-slice transport and final statement/raw-axiom/coherence gates must all pass before restoration.',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(E/'v197-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Three exact parser bodies and nine library bodies recorded; full kernel/row closure pending.')

L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
owned=(L/'PV_RDCD4_BytesSource.lean').read_text()
assert owned.count('PV_RDCD5_ParserRange.index')==3
assert 'PV_RDCD4_SliceRange194.index' not in owned
rng=(L/'PV_RDCD5_ParserRange.lean').read_text()
assert 'else fail .panic' in rng and 'else fail .arrayOutOfBounds' not in rng
ref=(L/'PV_RDCD5_V197.lean').read_text()
assert ref.count('else fail .panic')==2 and 'fail .arrayOutOfBounds' not in ref
old=subprocess.check_output(['git','show','a9aa230d1e:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD4_BytesSource.lean'],text=True)
assert old.replace('import R1Z.PV_RDCD4_SliceRange194','import R1Z.PV_RDCD5_ParserRange').replace('PV_RDCD4_SliceRange194.index','PV_RDCD5_ParserRange.index')==owned
config=json.load(open(R/'evidence/pv-rdcd5-20261101/deployed-config-reuse.json'))
assert config['configuration']
out.update(before_model=old,after_model=owned,correction='Only the three range calls and their import change in BytesSource. The helper uses identical ordered/bounded predicate and backing window, returning panic on invalid ranges. No branch, input, None or successful value is dropped.',complete_transport='R1Z.PV_RDCD5_ParserTransport.quartic : forall bytes : Slice U8, existing(bytes) = qm(bytes.val)',deployed_configuration_reused='evidence/pv-rdcd5-20261101/deployed-config-reuse.json',configuration_sha256=hashlib.sha256((R/'evidence/pv-rdcd5-20261101/deployed-config-reuse.json').read_bytes()).hexdigest(),wrong_kind_consequence='V197 only: local short_failure plus historical mismatch diagnostic; no restored consumer depends on wrong kind',negative_controls='Replacing panic by arrayOutOfBounds or restoring any old range call is rejected by the structural source gate; syntactic controls only, not Kani or native universal proofs')
(E/'v197-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Corrected range failure and all three parser call sites checked; V197 source structural gate complete; kernel/cohort gates pending.')

# Bind the source's terminal range-failure dispatch explicitly; never infer its
# error constructor from a theorem about successful windows.
fail_body=span(lib['slice/index.rs']['text'],'const fn slice_index_fail(', 'const fn slice_index_fail(')
assert fail_body.count('const_panic!(')==4
assert fail_body.index('if start > len') < fail_body.index('if end > len') < fail_body.index('if start > end')
def schema(range_text,owned_text,reference_text):
 return ('else fail .panic' in range_text and 'else fail .arrayOutOfBounds' not in range_text
  and owned_text.count('PV_RDCD5_ParserRange.index')==3
  and 'PV_RDCD4_SliceRange194.index' not in owned_text
  and reference_text.count('else fail .panic')==2
  and 'fail .arrayOutOfBounds' not in reference_text)
assert schema(rng,owned,ref)
controls=[]
for label,r2,o2,f2 in [
 ('wrong range constructor',rng.replace('else fail .panic','else fail .arrayOutOfBounds'),owned,ref),
 ('one legacy range call',rng,owned.replace('PV_RDCD5_ParserRange.index','PV_RDCD4_SliceRange194.index',1),ref),
 ('wrong late reference constructor',rng,owned,ref.replace('else fail .panic','else fail .arrayOutOfBounds',1))]:
 assert not schema(r2,o2,f2),label
 controls.append(dict(mutation=label,status='REJECTED by syntactic structural-schema control; no compiled fidelity claim'))
out.update(range_failure_dispatch=dict(path=lib['slice/index.rs']['path'],file_sha256=lib['slice/index.rs']['sha256'],body=fail_body,body_sha256=hashlib.sha256(fail_body.encode()).hexdigest(),binding='All four terminal arms invoke const_panic!, represented as fail.panic at the existing source/Result projection. Fixed parser ranges are ordered, so failed bounds reach the end>len arm. No arrayOutOfBounds constructor exists in this Rust dispatch.',fmt_qualification='No Aeneas.Std fmt value law is used. Panic diagnostics, writer state/errors, allocation, timing and abort/world observations remain physical-observer/runtime obligations; no always-Ok formatter claim.'),syntactic_negative_controls=controls)
(E/'v197-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Explicit terminal panic dispatch and three syntactic mutation controls checked.')
