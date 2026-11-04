"""Partial own-1: original initial Vec constructor and source-place identity.

Records exact deployed-source bodies and checks the constructor/receiver chain.
Does not assert all reached callers, native memory, or allocator adequacy.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

E = Path('evidence/pv-evhB-20261103')
REV = 'a5b8b16cf10ae7fa94a493a4e4723cefd83d3d1c'
STD = 'evidence/pv-v263-20261102/inputs/std-1.94.1/'
ADOPTED = json.loads((Path('evidence/pv-evh10-20261102') /
                      'adopted-backend-confirmation.json').read_text())
APP_REV = ADOPTED['adopted_build_receipt']['revision']
sha = lambda b: hashlib.sha256(b).hexdigest()


def read(rev, path):
    return subprocess.check_output(['git', 'show', f'{rev}:{path}'])


graph_path = ADOPTED['adopted_getrandom']['graph_path']
graph_bytes = read(APP_REV, graph_path)
assert sha(graph_bytes) == ADOPTED['adopted_getrandom']['graph_sha256']
graph = json.loads(graph_bytes)
selected_unit = next(u for u in graph['units']
                     if u['target']['name'] == 'aspis_r1_cost_probe')
assert selected_unit['features'] == [
    'ct-host-prover', 'default', 'private-leaf-salts', 'prover', 'r1p-check']
assert selected_unit['profile']['name'] == 'client'
assert selected_unit['profile']['opt_level'] == '3'
assert selected_unit['profile']['panic'] == 'abort'
assert selected_unit['profile']['debug_assertions'] is False
assert selected_unit['profile']['overflow_checks'] is False


def body(raw, anchor):
    text = raw.decode()
    start = text.index(anchor)
    brace = text.index('{', start)
    end, depth = brace + 1, 1
    # These selected bodies have no braces in string literals/comments.
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return dict(first=text[:start].count('\n')+1,
                last=text[:end].count('\n')+1, text=text[start:end])


vec = read(REV, STD+'alloc/src/vec/mod.rs')
raw = read(REV, STD+'alloc/src/raw_vec/mod.rs')
assert sha(raw) == '0c006d1bedcc8c1aa6d8f37ad5553e1b14c452c732745612cf23c4663c090965'
rows = []
for path, source, anchor, required, model in [
    ('alloc/src/vec/mod.rs', vec, 'pub const fn new() -> Self',
     ['Vec { buf: RawVec::new(), len: 0 }'],
     'emptyHeader.len=0; newAt mints the result lifetime'),
    ('alloc/src/raw_vec/mod.rs', raw, 'pub(crate) const fn new() -> Self',
     ['Self::new_in(Global)'],
     'constructor is Global, not an arbitrary allocator selection'),
    ('alloc/src/raw_vec/mod.rs', raw, 'pub(crate) const fn new_in(alloc: A)',
     ['T::LAYOUT.size() % T::LAYOUT.align() == 0',
      'RawVecInner::new_in(alloc, Alignment::of::<T>())', '_marker: PhantomData'],
     'shape and alignmentAddress interpret the same T; numeric interpretation OPEN'),
    ('alloc/src/raw_vec/mod.rs', raw, 'const fn new_in(alloc: A, align: Alignment)',
     ['Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()))',
      'Self { ptr, cap: ZERO_CAP, alloc }'],
     'emptyHeader: pointer=alignmentAddress, stored cap=0, dangling=true'),
    ('alloc/src/vec/mod.rs', vec, 'pub fn try_reserve_exact(&mut self, additional: usize)',
     ['self.buf.try_reserve_exact(self.len, additional)'],
     'receiverWorld selects the source local lifetime; borrow keeps that lifetime'),
    ('alloc/src/raw_vec/mod.rs', raw, 'pub(crate) fn try_reserve_exact(',
     ['self.inner.try_reserve_exact(len, additional, T::LAYOUT)'],
     'buf/inner projections preserve the enclosing Vec lifetime, not element equality'),
]:
    span = body(source, anchor)
    for item in required:
        assert item in span['text'], (anchor, item)
    rows.append(dict(revision=REV, path=STD+path, file_sha256=sha(source),
                     anchor=anchor, source=span, model=model))

app_rows = []
for path, anchor, required in [
    ('crates/aspis-r1-cost-probe/src/prover.rs', 'fn derive_private_salts(',
     ['let mut salts=Vec::new();salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT)',
      'let mut result=Ok(salts);', 'Ok(salts)=>derive_private_salt_step(',
      'Err(error)=>Err(error)', 'result.map(PrivateSalts::new)']),
    ('crates/aspis-r1-cost-probe/src/prover.rs', 'fn derive_private_salt_step(',
     ['mut salts:Vec<[u8;32]>', '.map_err(|_|Error::Semantic)?;',
      'salts.push(salt);', 'Ok(salts)']),
    ('crates/aspis-r1-cost-probe/src/host_commitment.rs',
     'pub fn new(values: Vec<[u8; 32]>)', ['Self(values)']),
]:
    current, adopted = read('HEAD', path), read(APP_REV, path)
    span = body(current, anchor)
    assert span['text'] == body(adopted, anchor)['text']
    for item in required:
        assert item in span['text'], (anchor, item)
    app_rows.append(dict(path=path, adopted_revision=APP_REV,
                         file_sha256=sha(current), adopted_file_sha256=sha(adopted),
                         source=span))

lean = Path('lean/PV_EVHB_SourceLifetimes.lean').read_bytes()
for fragment in [
    'places : Place → Option Nat', 'next := s.next+1',
    'world := store s.world s.next (emptyHeader shape alignmentAddress)',
    '(s.places p).map (fun id => PV_EVHB_OwnerRegistry.project id s.world)',
    'if q=target then s.places source else if q=source then none else s.places q',
    '| some id => {s with world := install s.world id h pointer cap}',
]:
    assert fragment in lean.decode(), fragment

record = dict(
    evidence_class='PARTIAL own-1 structural constructor/receiver binding; not complete reached native association',
    resume_revision='26bc9dfd6b',
    adopted_client_sha256=ADOPTED['adopted_build_receipt']['receipt']['sha256'],
    toolchain=ADOPTED['adopted_build_receipt']['receipt']['toolchain'],
    deployment=dict(unit_graph_revision=APP_REV, unit_graph_path=graph_path,
                    unit_graph_sha256=sha(graph_bytes),
                    units=[dict(package=u['pkg_id'], target=u['target']['name'],
                                kind=u['target']['kind'], features=u['features'],
                                profile=u['profile']) for u in graph['units']],
                    scope='Original source bodies unchanged at adopted revision; no new build/extraction/harness'),
    std_source=rows, original_source=app_rows,
    lean_path='lean/PV_EVHB_SourceLifetimes.lean', lean_sha256=sha(lean),
    constructor_prefix=dict(
        source='original derive_private_salts: Vec::new followed immediately by salts.try_reserve_exact',
        source_place='saltsLocal activation = {activation, fields=[0]}',
        lifetime='pre-constructor State.next, monotonically incremented by newAt',
        receiver='computed by receiverWorld from the constructor-installed place',
        proof='original_initial_receiver / constructor_receiver / constructor_selection',
        freshness='new_fresh / constructor_distinct, under Fresh on the input place environment'),
    move_scope=dict(
        proof='move_receiver / move_fresh / move_selection',
        model='source-place transport preserves lifetime-indexed header and allocator world',
        source_binding='move mechanism only; full original control/drop interpreter remains OPEN'),
    remaining=[
        'Original extracted entry must construct State and activation identities, with Fresh and vacant destination invariants.',
        'Bind shape/alignmentAddress to actual T layout and without_provenance interpretation, including ZST and numeric limits.',
        'Install enum/argument/return/PrivateSalts payload moves in original control flow, including error-triggered drop and nonreturn prefixes.',
        'Select receiverWorld at every reached call and thread the resulting world back into that same source state.',
        'Bind actual Global/System primitives and complete returning macro projection to V183 (rdea-1).',
        'Derive unchanged reached_reserve_header_delivery and v263 descriptor-view instance only after the preceding constructions.',
    ],
    source_to_machine='V370 retained; no physical stack/frame premise added to source-level projections',
    reached_reserve_header_delivery='OPEN', v263_descriptor_view='OPEN',
    trust_fields_added=[], endpoint_rows_removed=[])
out = json.dumps(record, indent=2)+'\n'
dest = E/'lifetime-source-D588.json'
if '--check' in sys.argv:
    assert dest.read_text() == out
else:
    dest.write_text(out)
print('PASS six std constructor/receiver spans and three original bodies; partial own-1 only')
