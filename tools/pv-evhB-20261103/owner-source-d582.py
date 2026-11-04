"""Check the exact source stores behind the descriptor-local owner construction.

This is a PARTIAL own-1 structural binding, not a deployed owner selector,
allocator adequacy proof, or generic reserve/push correspondence.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

REV = 'a5b8b16cf10ae7fa94a493a4e4723cefd83d3d1c'
PATH = 'evidence/pv-v263-20261102/inputs/std-1.94.1/alloc/src/raw_vec/mod.rs'
SHA = '0c006d1bedcc8c1aa6d8f37ad5553e1b14c452c732745612cf23c4663c090965'
E = Path('evidence/pv-evhB-20261103')
raw = subprocess.check_output(['git', 'show', f'{REV}:{PATH}'])
assert hashlib.sha256(raw).hexdigest() == SHA
source = raw.decode()
lean = Path('lean/PV_EVHB_RawVecOwner.lean').read_text()
control = Path('lean/PV_EVHB_RawVecSource.lean').read_text()
projection = Path('lean/PV_EVHB_RawVecProjection.lean').read_text()
registry = Path('lean/PV_EVHB_OwnerRegistry.lean').read_text()


def span(start, end):
    a = source.index(start)
    b = source.index(end, a) + len(end)
    return dict(first=source[:a].count('\n')+1,
                last=source[:b].count('\n')+1, text=source[a:b])


rows = [
    dict(item='RawVecInner fields', model='Header.cap is raw, stored capacity',
         source=span('struct RawVecInner<A: Allocator = Global> {', '\n    alloc: A,\n}')),
    dict(item='new_in', model='dangling pointer evidence; physical cap zero',
         source=span('const fn new_in(alloc: A, align: Alignment)', 'Self { ptr, cap: ZERO_CAP, alloc }')),
    dict(item='capacity', model='public capacity is distinct for ZST; not yet a Vec-capacity adapter',
         source=span('const fn capacity(&self, elem_size: usize)',
                     'if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }')),
    dict(item='finish_grow', model='allocated_pending; allocated_lookup; old header unchanged',
         source=span('unsafe fn finish_grow(', '\n            Err(_) => Err(AllocError { layout: new_layout, non_exhaustive: () }.into()),\n        }')),
    dict(item='set_ptr_and_cap', model='pointerStore then capacityStore; install_lookup; pending_install',
         source=span('const unsafe fn set_ptr_and_cap(',
                     'self.cap = unsafe { Cap::new_unchecked(cap) };')),
    dict(item='grow_exact', model='caller commits only after successful finish_grow; full branch interpreter OPEN',
         source=span('unsafe fn grow_exact(', '\n        Ok(())\n    }')),
    dict(item='grow_amortized', model='caller commits only after successful finish_grow; full branch interpreter OPEN',
         source=span('unsafe fn grow_amortized(', '\n        Ok(())\n    }')),
    dict(item='shrink_unchecked', model='zero deallocation/reset and nonzero resize/commit; source interpreter OPEN',
         source=span('unsafe fn shrink_unchecked(', '\n        Ok(())\n    }')),
    dict(item='deallocate', model='deallocate_consumes; does not clear header; native dealloc adequacy rdea-1',
         source=span('unsafe fn deallocate(&mut self, elem_layout: Layout)',
                     '\n        }\n    }')),
    dict(item='RawVec drop', model='consumes old ownership; not preservation of live old allocation',
         source=span('unsafe impl<#[may_dangle] T, A: Allocator> Drop for RawVec<T, A>',
                     '\n    }\n}')),
]
stores = rows[4]['source']['text']
assert stores.index('self.ptr = Unique::from(ptr.cast());') < stores.index('self.cap =')
finish = rows[3]['source']['text']
assert '&self,' in finish and 'self.ptr =' not in finish and 'self.cap =' not in finish
for i in (5, 6):
    body = rows[i]['source']['text']
    assert body.index('self.finish_grow(cap, elem_layout)?') < body.index('self.set_ptr_and_cap(ptr, cap)')
dealloc = rows[8]['source']['text']
assert 'self.alloc.deallocate(ptr, layout)' in dealloc
assert 'self.ptr =' not in dealloc and 'self.cap =' not in dealloc
assert 'store (store w owner (pointerStore h pointer)) owner' in lean
assert '(capacityStore (pointerStore h pointer) cap)' in lean
for fragment in (
    'if h.shape.width=0 then lift (.ok (.error .capacityOverflow))',
    'else if h.len+additional>wordMax then lift (.ok (.error .capacityOverflow))',
    'max (minCap h.shape.width) (max (h.cap*2) (len+additional))',
    'if h.shape.width=0 ∨ h.cap=0 then runtime.allocate h cap else runtime.grow h cap',
    '| .capacityOverflow => runtime.capacityOverflow',
    '| .allocError layout => runtime.handleAllocError layout',
    '| .returned (.fail e) => ⟨.returned (.fail e),r.world,r.events⟩',
    '| .returned .div => ⟨.returned .div,r.world,r.events⟩',
    '| .fault e => ⟨.fault e,r.world,r.events⟩',
    '| .exhausted => ⟨.exhausted,r.world,r.events⟩',
):
    assert fragment in control, fragment

record = dict(
    evidence_class='PARTIAL own-1 structural binding of descriptor stores and phase boundaries; NOT a complete native interpreter',
    resume_revision='9f6c615e29', source_revision=REV, source_path=PATH, source_sha256=SHA,
    lean_path='lean/PV_EVHB_RawVecOwner.lean',
    lean_sha256=hashlib.sha256(lean.encode()).hexdigest(), rows=rows,
    control_path='lean/PV_EVHB_RawVecSource.lean',
    control_sha256=hashlib.sha256(control.encode()).hexdigest(),
    projection_path='lean/PV_EVHB_RawVecProjection.lean',
    projection_sha256=hashlib.sha256(projection.encode()).hexdigest(),
    registry_path='lean/PV_EVHB_OwnerRegistry.lean',
    registry_sha256=hashlib.sha256(registry.encode()).hexdigest(),
    constructed_returning_registry='OwnerRegistry; source-place/store and model header-delivery laws; actual native instance OPEN',
    allocator_metadata_transitions='specified returning semantics; native Global/System adequacy retained under rdea-1',
    source_to_machine='V370 retained',
    original_caller_slot_interpretation='OPEN',
    reached_reserve_header_delivery='OPEN', v263_D579_instance='OPEN',
    same_OWNED_at_every_internal_boundary='false for successful realloc before header commit, and for consumed drop',
    reserve_return_boundary_counterexample='NOT established',
    full_failure_and_abort_interpreter='OPEN',
    returning_source_control='local model only: reserve/exact/amortized guards, allocation selection, commit, drop, error dispatch',
    missing_source_bindings=[
        'constructors and reached source receiver to owner-slot identity',
        'initialization and same native header/value interpretation',
        'allocator-side active-owner registry preserved by source calls',
        'full source-execution to registry macro-step returning projection, retaining nonreturning native runs separately',
        'Global/System primitive request/outcome/event association',
        'numeric checked/wrapping/layout interpretation under admitted ABI',
        'shrink reachability and source interpreter',
        'push value store and length store; existing v263 carriers/instance',
        'diagnostic/panic/abort primitives and all nonreturning prefixes',
    ],
    trust_fields_added=[], endpoint_rows_removed=[])
out = json.dumps(record, indent=2) + '\n'
dest = E/'owner-source-D582.json'
if '--check' in sys.argv:
    assert dest.read_text() == out
else:
    dest.write_text(out)
print('PASS 10 pinned RawVec source spans; partial store/phase binding only; generic correspondence OPEN')
