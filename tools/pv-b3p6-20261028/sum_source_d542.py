"""own-1 structural binding of the deployed sum_high, including its std cone.
Not a machine proof. All loops bind to already proved named symbolic laws.
"""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028/resume17');ns={}
exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
index,tokens=ns['index'],ns['tokens'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=Path('crates/aspis-r1-cost-probe/src/host_terminal.rs');s=p.read_text();f=next(f for f in index(s)if f['name']=='sum_high')
assert tokens(f['body'])==tokens('''{let mut sum = QM31::ZERO;for range in ranges {for block in range.clone() {sum = sum.add(selectors.high[block]);}}sum}''')
pins=json.loads((D/'deployed-source-pins.json').read_text());assert sha(p)==pins[str(p)]
report=json.loads((D/'K3-STD-PARITY-D540.json').read_text());rows=[r for r in report['rows']if r['group']=='K73946'];support=[]
def item(part,body):
 rr=[r for r in rows if part in r['name']];assert len(rr)==1,(part,len(rr));r=rr[0];assert r['status']=='IDENTICAL';it=r['deployed_item'];assert tokens(it['body'])==tokens(body)
 q=D/'std-sources'/(r['source']+'.deployed');assert sha(q)==report['files'][r['source']]['deployed_sha256'];assert it['body']in q.read_text();support.append(r)
item('IntoIterator for &[std::ops::Range<usize>]','{ self.iter() }')
item('core::slice::<impl [std::ops::Range<usize>]>::iter','{ Iter::new(self) }')
item("std::slice::Iter::<'_, std::ops::Range<usize>>::new",'''{let len = slice.len();let ptr: NonNull<T> = NonNull::from_ref(slice).cast();unsafe {let end_or_len = if T::IS_ZST { without_provenance(len) } else { ptr.as_ptr().add(len) };Self { ptr, end_or_len, _marker: PhantomData }}}''')
item('<std::ops::Range<usize> as std::iter::IntoIterator>::into_iter','{ self }')
item('std::iter::range::<impl std::iter::Iterator for std::ops::Range<usize>>::next','{ self.spec_next() }')
item('RangeIteratorImpl>::spec_next','{ if self.start < self.end { let old = self.start; self.start = unsafe { Step::forward_unchecked(old, 1) }; Some(old) } else { None } }')
item('<usize as std::iter::Step>::forward_unchecked','{ unsafe { start.unchecked_add(n as Self) } }')
r=next(r for r in rows if 'std::slice::Iter<' in r['name']and r['name'].endswith('>::next'));it=r['deployed_item'];assert r['status']=='IDENTICAL'
# Check complete item against the captured body plus all branch/store landmarks.
q=D/'std-sources'/(r['source']+'.deployed');assert sha(q)==report['files'][r['source']]['deployed_sha256'];assert it['body']in q.read_text()
for snippet in ['let ptr = self.ptr;', 'let end_or_len = self.end_or_len;', 'if T::IS_ZST', 'return None;', 'self.ptr = ptr.add(1);', 'Some({ptr}.$into_ref())']:
 assert snippet in it['body']
support.append(r)
q=D/'std-sources/core/src/ops/range.rs.deployed';rs=q.read_text();assert '#[derive_const(Clone, Default, PartialEq)]'in rs
assert 'pub struct Range<Idx> {'in rs and 'pub start: Idx,'in rs and 'pub end: Idx,'in rs
assert 'Drop for Range<' not in rs
steps=[
 dict(source='let mut sum = QM31::ZERO',model='source_sum_ranges13 selectors.high ranges ZERO',argument='Same exact field constant; local accumulator only, no write through shared inputs.'),
 dict(source='for range in ranges: &[Range<usize>]',model='List recursion of source_sum_ranges13',argument='Bind concrete slice to its ordered list of (start,end) values and retain the shared loan identity. IntoIterator calls slice.iter -> Iter::new. Range<usize> is non-ZST (two usize fields). Relate ptr=base+j, end=base+len to list suffix drop j. next compares ptr==end: equality returns None, otherwise increments ptr once and returns &ranges[j]. On every j<len, pointer arithmetic and reference are inside a live immutable allocation; next never mutates any range. At j=len (including len=0) no element is read. Each source next corresponds exactly to one cons or nil case; duplicates and order are preserved. ZST branch in the generic body is unreachable for this instantiation. Pointer/layout/lowering is retained V370.'),
 dict(source='range.clone()',model='pair (start,finish) passed by value to range_loop13',argument='Range<usize> has exactly start/end fields; its derived Clone copies both usize values, with usize Clone the value identity. This generated expansion is explicitly V370 D381/D386, not proved by source-template identity. The borrowed original range remains unchanged; clone has no custom destructor and its two usize fields have effect-free drops. Shared slice iterator is also a pointer/marker record with no custom destructor. Drop glue remains V370; no runtime effect is elided.'),
 dict(source='for block in cloned Range<usize>',model='range_next13 / range_body13 / range_loop13',argument='IntoIterator is identity, next delegates to checked TrustedStep spec_next. If start>=finish both return none without increment or body (including reversed or MAX endpoints). Otherwise both yield old start and store successor before the body. range_increment_safe13 proves start.val+1<size Usize from start<finish, so unchecked_add and wrapping_add are equal, never UB. range_body_binding13 and range_loop_binding13 then preserve complete Result iteration, with the same cursor at each step; no concrete range is normalized.'),
 dict(source='selectors.high[block]',model='sum_step high uses Array.index_usize',argument='Exactly high[block], before the add and store. Bound block<64 gives the same immutable field element. If block>=64 source panics and the local Result model fails at that same access, before add/store and before any later range. Panic formatting/abort observations belong to the separately open std/D159 source cone; this local Result association does not claim to erase their observer effects.'),
 dict(source='sum = sum.add(element)',model='same extracted aspis_core.field.QM31.add, then local state replacement',argument='Identical field callee on both sides, no multiplication or arithmetic abstraction. Keep its full Result, propagate failure/divergence and replace sum only on success. Every field-limb operation remains in the pinned extraction/tool trust; no reassociation, commutation, narrowing, or canonical input assumption.'),
 dict(source='loop cleanup and final sum',model='range_drop13, list nil -> Result.ok sum',argument='No side-effecting destructor: Range<usize> owns two integers; Iter owns pointers and PhantomData. The shared slice and selectors remain live and unchanged, including error/unwind. range_drop_binding13 is the exact effect-free cleanup; iterator/drop compiler glue is retained V370. At list end return the accumulator once. sum_ranges_binding13 gives reference equality on every ordered range list, and native_sum_high_binding15 retains both shared loan identities.')]
calllines=[dict(line=i,text=l.strip())for i,l in enumerate(s.splitlines(),1)if 'sum_high(selectors,'in l]
assert len(calllines)==3
out=dict(body='host_terminal::sum_high',route='k-prime route3 / own-1 script-checked structural source argument; not machine proof',source=dict(path=str(p),sha256=sha(p),item=f),steps=steps,std_support=support,range_declaration=dict(path=str(q),sha256=sha(q)),compiled_symbolic_laws=['PV_B3P_Binding13227.range_increment_safe13','PV_B3P_Binding13227.range_body_binding13','PV_B3P_Binding13227.range_loop_binding13','PV_B3P_Binding13227.range_drop_binding13','PV_B3P_Binding13227.sum_ranges_binding13','PV_B3P_Binding13227.sum_high_link13','PV_B3P_Native15227.native_sum_high_binding15'],call_sites=calllines,domain='Every high array and every valid immutable slice of Range<usize>, including reversed/empty/out-of-bounds ranges; typed source-to-Result association with failures retained. All three actual interval lists covered, no canonicality restriction.',V370='Exact derived Range<usize>::clone, usize Clone identity, Range/Iter drop glue, pointer intrinsics and source-to-machine preservation retained at owner D381/D386.',D188='No writes through mutable borrows in this source body. Iterator cursor and accumulator stores are local. No discarded restoration continuation introduced.',scope='Local source body association; full std panic/format observer cone, matrix/callback closure and V244 endpoint remain OPEN.',budget_spent=dict(lean=0,extraction=0,kani=0,native=0))
(D/'SUM-SOURCE-BINDING-D542.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(source_statements=len(steps),std_items=len(support),actual_call_sites=len(calllines))))
