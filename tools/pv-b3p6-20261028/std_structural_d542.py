"""k''' structural source arguments, not a machine proof. Read-only captures.
Fail closed on any changed body or uncovered ordinary item. No native build.
"""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028/resume17')
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((D/'STD-ITEM-INVENTORY-D540.json').read_text())
reports=[json.loads((D/n).read_text())for n in ['STD-PARITY-D540.json','K3-STD-PARITY-D540.json']]
checks=[];support=[]
def eq(a,b):assert tokens(a)==tokens(b),(a,b)
def file(rel,side='deployed'):
 p=D/'std-sources'/(rel+'.'+side);s=p.read_text()
 for r in reports:
  if rel in r['files']:assert sha(p)==r['files'][rel][side+'_sha256']
 return p,s
for a in json.loads((D/'STD-SUPPLEMENT-D542.json').read_text()):assert sha(Path(a['path']))==a['sha256']
def fn(rel,name,body,context=None,side='deployed'):
 p,s=file(rel,side);rr=[f for f in index(s)if f['name']==name and (context is None or any(context in c for c in f['context']))]
 assert len(rr)==1,(rel,name,context,rr)
 r=rr[0];eq(r['body'],body);support.append(dict(path=str(p),file_sha256=sha(p),item=r));return r
fn('core/src/mem/maybe_dangling.rs','new','{ MaybeDangling(x) }')
fn('core/src/mem/maybe_dangling.rs','as_mut','{ &mut self.0 }')
p,s=file('core/src/mem/maybe_dangling.rs');assert '#[repr(transparent)]'in s and 'pub struct MaybeDangling<P: ?Sized>(P);'in s
fn('core/src/cmp.rs','ne','{ !self.eq(other) }','trait PartialEq')
fn('core/src/slice/cmp.rs','eq','{ SlicePartialEq::equal(self, other) }','PartialEq<[U]>')
fn('core/src/ops/try_trait.rs','call_mut','{ NeverShortCircuit((self.f)(args)) }','Wrapped<T, A, F>')
fn('core/src/ops/try_trait.rs','branch','{ ControlFlow::Continue(self.0) }','Try for NeverShortCircuit')
fn('core/src/array/mod.rs','try_from_fn_erased','''{
 let mut guard = Guard { array_mut: buffer, initialized: 0 };
 while guard.initialized < guard.array_mut.len() {
 let item = generator(guard.initialized).branch()?;
 unsafe { guard.push_unchecked(item) };
 }
 mem::forget(guard); ControlFlow::Continue(())
}''')
fn('core/src/array/mod.rs','try_from_trusted_iterator','''{
 assert!(iter.size_hint().0 >= N);
 fn next<T>(mut iter: impl UncheckedIterator<Item = T>) -> impl FnMut(usize) -> T {
 move |_| { unsafe { iter.next_unchecked() } }
 }
 try_from_fn(next(iter))
}''',side='kani')
fn('core/src/array/drain.rs','new','''{
 let ptr: NonNull<T> = NonNull::from_mut(array).cast();
 unsafe { let end = if T::IS_ZST { null_mut() } else { ptr.as_ptr().add(N) };
 Self { ptr, end, f, l: PhantomData } }
}''')
fn('core/src/array/drain.rs','call_mut','''{
 if T::IS_ZST { (self.f)(unsafe { conjure_zst::<T>() }) }
 else { let p = self.ptr; self.ptr = unsafe { self.ptr.add(1) };
 (self.f)(unsafe { p.read() }) }
}''')
arguments={
'ub':("{ intrinsics::ub_checks() && const_eval_select!(@capture { } -> bool: if const { false } else { !cfg!(miri) }) }", "{ const_eval_select!(@capture { } -> bool: if const { false } else { !cfg!(miri) }) && intrinsics::ub_checks() }", 'Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.'),
'wrap':('{ move |a| NeverShortCircuit(f(a)) }','{ Wrapped { f, p: PhantomData } }','Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.'),
'mdnew':('{ ManuallyDrop { value } }','{ ManuallyDrop { value: MaybeDangling::new(value) } }','MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.'),
'mdmut':('{ &mut self.value }','{ self.value.as_mut() }','The checked MaybeDangling::as_mut returns &mut self.0. Under old value ~ new value.0, both yield the exclusive reference to the same live [QM31;4] storage. Its four elements have valid integer fields and no destructor. The borrow is held by the array drain; the underlying stack array remains alive and is not separately dropped. No added branch, panic, UB check, allocation or callback.'),
'ne':('{ SlicePartialEq::not_equal(self, other) }',None,'The removed slice override delegates to removed not_equal, whose checked body is !self.equal(other). Deployed PartialEq::ne default is checked as !self.eq(other), and deployed slice eq delegates to SlicePartialEq::equal. Substitution yields the same single equal call on the same slices and negates its Boolean result once. The equal body remains token-identical in the D540 reached-item audit, including length mismatch, indexed M31 comparisons and early exit. No added reads, comparisons, panic or UB check. Derived M31 equality lowering remains V370.'),
'not_equal':('{ !self.equal(other) }',None,'This helper has no independent caller beyond slice ne in this gate. Its continuation !equal(self,other) is substituted by the checked deployed PartialEq::ne -> slice eq -> SlicePartialEq::equal path. Same lengths, element reads, early returns and negation; equal is token-identical. No new panic or UB branch.'),
'map':('{ drain_array_with(self, |iter| try_from_trusted_iterator(iter.map(f))) }','{ let mut me = ManuallyDrop::new(self); let mut f = unsafe { drain::Drain::new(&mut me, &mut f) }; try_from_fn(&mut f) }','Reached T=QM31, N=4, R=NeverShortCircuit<[u32;4]>. Relate old remaining IterMut to new [ptr,end) and old initialized output prefix to the new Guard prefix. Initially both own exactly input[0..4], output empty. At step j<4 both advance the source cursor before reading input[j], invoke the same extension_limbs once, branch Continue, write output[j], advance initialized. NeverShortCircuit has no residual inhabitant. Old size_hint lower bound is exactly 4, so its removed assert!(>=4) cannot panic. Both call try_from_fn/erased with the same 4 callbacks; support bodies are checked. At exit both forget the full Guard and return the same initialized array. If a callback panics, both drop the same remaining input suffix and initialized output prefix; these are destructor-free QM31/[u32;4], so relative guard/function-drop order has no observable effect. extension_limbs is a pure field projection. Both pointer walks stay in the live array, never read end, and use the same four UB-valid accesses. ZST branch is unreachable for QM31. Pointer/layout/glue lowering remains V370.'),
'drain_helper':('{ let mut array = ManuallyDrop::new(array); let drain = Drain(array.iter_mut()); func(drain) }',None,'Removed helper is inlined into deployed try_map: old ManuallyDrop stack owner plus IterMut maps to new ManuallyDrop stack owner plus Drain::new(ptr,end,f). The only reached func is the try_map closure feeding trusted map to try_from_fn. Both owners stay live across four callbacks and suppress the original array drop. Relate remaining elements by index j as in the try_map argument, including unwind. No escaping pointer or alias; added Drain::new end pointer is one-past a live four-element non-ZST array. Removed size assertion is true (4>=4).'),
'next':('{ let p: *const T = unsafe { self.0.next_unchecked() }; unsafe { p.read() } }',None,'Removed next_unchecked maps to the checked new Drain::call_mut non-ZST arm: let p=ptr; ptr=ptr.add(1); f(p.read()). At each j<4 the old IterMut next_unchecked yields address input[j] and advances before read; new ptr does the same. Map f is invoked once afterwards. No call at j=4; same valid aligned initialized locations, same ownership transfer and panic suffix. QM31 is non-ZST with no destructor. Intrinsic pointer semantics stay V370.'),
'len':('{ self.0.len() }',None,'Only the old trusted-array preflight consumes len through size_hint: initial remaining IterMut length is 4. New try_map passes the type-level N=4 to try_from_fn, whose guard iterates exactly 4 times; no length query is exposed to a caller. At intermediate j the relation is old len=4-j and new end-ptr=4-j. The only removed size assertion is true. No changed result/panic/UB behaviour.'),
'hint':('{ let n = self.len(); (n, Some(n)) }',None,'The sole reached size_hint consumer is try_from_trusted_iterator at initial j=0. ExactSizeIterator yields (4,Some(4)); it tests only lower>=4, which is true. Deployed try_map uses try_from_fn with fixed N=4, so erasing this true preflight and unused Some bound preserves all effects and failures. len and cursor relation are checked in the same structural family.'),
'drop':('{ unsafe { drop_in_place(self.0.as_mut_slice()) } }','{ if !T::IS_ZST { let slice = unsafe { from_raw_parts_mut::<[T]>(self.ptr.as_ptr(), self.end.offset_from_unsigned(self.ptr.as_ptr()),) }; unsafe { drop_in_place(slice) } } }','Reached T=QM31 is non-ZST and has only four u32 field limbs, no Drop implementation. At every normal or panic exit, old IterMut remaining slice and new [ptr,end) denote precisely input[j..4]. Both drop that suffix once and never the moved prefix. Added offset_from_unsigned has same-allocation, ordered, aligned pointers by 0<=j<=4; empty j=4 is valid. No new failing UB check or panic. For this T all element drop glue is effect-free; output Guard drops initialized [u32;4] prefix, also effect-free. No general claim for ZST or side-effecting destructors; glue/layout semantics remain V370.')}
rows=[]
for r in x['ordinary_or_generated_nonidentical_items']:
 if r['classification']!='ordinary standard-library source item':continue
 n=r['name'];f=r['kani_item']['name'];rel=r['source']
 key=('ub' if f=='check_language_ub' else 'wrap' if f=='wrap_mut_1' else 'mdnew' if 'ManuallyDrop' in n and f=='new' else 'mdmut' if f=='deref_mut' else 'ne' if f=='ne' else 'not_equal' if f=='not_equal' else 'map' if f=='try_map' else 'drain_helper' if f=='drain_array_with' else 'next' if f=='next_unchecked' else 'len' if f=='len' else 'hint' if f=='size_hint' else 'drop' if f=='drop' else None)
 assert key is not None,n
 old,new,argument=arguments[key];eq(r['kani_item']['body'],old)
 if new is not None:eq(r['deployed_item']['body'],new)
 else:assert r['deployed_item']is None
 # Verify recorded full declarations are literal spans of their pinned captures.
 for side in ['kani','deployed']:
  p,s=file(rel,side);item=r[side+'_item']
  if item:assert item['body']in s and item['signature']in s
 rows.append(dict(**r,argument_key=key,structural_argument=argument,verdict='ARGUED under k-triple-prime'))
assert len(rows)==23,len(rows)
# Concrete source facts used by the reached drain argument.
field=Path('crates/aspis-core/src/field.rs').read_text();assert 'pub struct QM31' in field and 'impl Drop for QM31'not in field
poseidon=Path('tools/pv-b3p6-20261028/v244/deployed_poseidon_kani16.rs').read_text()
assert 'fn extension_limbs(value: QM31) -> [u32; 4] {\n    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]\n}' in poseidon
for a in (False,True):
 for b in (False,True):assert (a and b)==(b and a)
label="Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''')"
groups={g:dict(ordinary_items=[i for i,r in enumerate(rows)if g in r['groups']],ordinary_items_all_argued=True,credit='RELEASED: local equivalence only',label=label,compiler_items=[r['name']for r in x['ordinary_or_generated_nonidentical_items']if g in r['groups']and r['classification'].startswith('V370')],remaining='V370 D381/D386 retained; actual caller domains and whole-row composition remain separate')for g in ['transition','external','internal','K73946','K73948']}
# Historical K3 audit already inspected these specific selected harnesses.
k3=json.loads((D/'K3-AUDIT-D537.json').read_text());assert len(k3['selected'])==18
assert all(not r['writable_statics_in_harness_stubs_or_oracles']for r in k3['selected'])
out=dict(rule="k''' / LOG D542",label=label,method=__doc__,inventory_sha256=sha(D/'STD-ITEM-INVENTORY-D540.json'),groups=groups,items=rows,support_items=support,unargued_ordinary_items=[],K3='Historical selected harness audit reused; K73946/K73948 dedicated static-free controls K73945/K73947 retained. No suspended result reinstated.',compiler_boundary='All intrinsics, closure lowering, derived methods and drop glue remain V370, owner D381/D386. Source structural argument only, no machine proof.',source_inputs={str(p):sha(p)for p in [Path('crates/aspis-core/src/field.rs'),Path('tools/pv-b3p6-20261028/v244/deployed_poseidon_kani16.rs')]},budget_spent=dict(lean=0,extraction=0,kani=0,native=0),endpoint_premise_changes=dict(removed=[],added=[],weakened=[]))
(D/'STD-STRUCTURAL-D542.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# D542 ordinary std structural arguments', '',label+'.','', 'Script-checked structural arguments; not machine proofs. All 23 ordinary instantiated items are argued. No ordinary blocker remains. V370 / D381/D386 retains intrinsics, generated glue and compiler preservation; no T field or endpoint premise changes. Historical K3 suspensions remain.','']
for g,v in groups.items():
 lines+=['## '+g,'','Credit RELEASED under k\'\'\' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.','']
 for i in v['ordinary_items']:
  r=rows[i];lines+=['### `'+r['name']+'`','',r['structural_argument'],'','Old ('+r['source']+':'+str(r['kani_item']['start'])+'):','```rust',r['kani_item']['body'],'```','', 'Deployed:','```rust',r['deployed_item']['body']if r['deployed_item']else '// Removed declaration: replacement path specified above; supporting bodies in JSON.','```','']
 lines+=['Retained compiler items: '+', '.join('`'+n+'`'for n in v['compiler_items'])+'.','']
lines+=['All source hashes, old/new full signatures, reached monomorphisations, supporting replacement bodies and original symbols are recorded in STD-STRUCTURAL-D542.json. Script: tools/pv-b3p6-20261028/std_structural_d542.py. No Kani/Lean/native build run in this source audit.','']
(D/'STD-STRUCTURAL-D542.md').write_text('\n'.join(lines))
print(json.dumps(dict(ordinary_items=len(rows),groups={g:len(v['ordinary_items'])for g,v in groups.items()},unargued=[])))
