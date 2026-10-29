"""Owned structural parser route only; no extractor/Kani rerun."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
lib={x['relative']:x for f in ['library-sources.json','v220-library-sources.json','v197-library-sources.json'] for x in json.load(open(E/f))}
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
('pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31>','pub fn from_le_bytes(bytes:&[u8])->Option<QM31>{let c0=CM31::from_le_bytes(&bytes[0..8])?;let c1=CM31::from_le_bytes(&bytes[8..16])?;Some(QM31{c0,c1})}','BytesSource.qm; V197.source_reference/frame','Take first8 before parsing c0; None returns without second-half range. Only successful c0 evaluates8..16 and c1. Returned QM31 contains no reference.')]:
 body=span(field,context,'pub fn from_le_bytes(');assert tok(body)==tok(expected),context
 apps.append(dict(context=context,body=body,expected=expected,body_sha256=hashlib.sha256(body.encode()).hexdigest(),model='R1Z.PV_RDCD4_'+model,source_steps=steps))
checks=[
('slice/index.rs','SliceIndex<[T]> for ops::Range<usize>','fn index(', 'Checked stop-start and stop<=length; success forms same readonly range via offset+length; failure is the original indexing failure carrier. Fixed parser bounds are ordered.','SliceRange194.success/reversed/oversized/length; ParserWindows.compose/no_write'),
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
 rows.append(dict(path=lib[path]['path'],file_sha256=lib[path]['sha256'],body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),source_steps=steps,model='R1Z.PV_RDCD4_'+model))
out=dict(row='V197',application_file='crates/aspis-core/src/field.rs',application_sha256=hashlib.sha256(field.encode()).hexdigest(),application_bindings=apps,library_bindings=rows,route='k-prime/own-1 exact owned Lean source reference. Pinned Aeneas escaping-reference loan-validation rejection remains recorded; no modified Rust, new extractor, Kani or loan-validation waiver.',before='Complete concrete parser source-to-reference Result law unbound at original arbitrary byte-slice input.',after_target='Same input, Option<QM31>, indexing-failure and short-circuit behavior; second-half bounds check stays after c0 None. Immutable input frame preserved, no returned borrow.',primitive_boundary='Typed pointer/read-only array4 copy and integer-layout/compiler semantics V370/D381/D386 retained. Native panic/observer/world obligations remain outside original Result abstraction.',pending='All six new parser modules, whole Result theorem and coherent source/object checks must pass before any restoration.',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(E/'v197-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Three exact parser bodies and nine library bodies recorded; full kernel/row closure pending.')
