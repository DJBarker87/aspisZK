#!/usr/bin/env python3
"""Read/hash-only frozen stage-2 cut inventory; no build or source rewrite.

The inventory counts explicit source declarations in the orchestration cut,
not Rust monomorphizations, generated trait impls or the recursively expanded
SDK/field backend. Those are explicit frontiers, as in the stage-1 kits.
"""
import argparse
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[5]
BASE = ROOT / 'docs/research/100bit-spend-path-20261013'
OUT = BASE / 'evidence/stage2-extraction-20261020'
REV = '9a71031d3'
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])
def dump(x):
    return (json.dumps(x, indent=2, sort_keys=True) + '\n').encode()

spec = importlib.util.spec_from_file_location('source_cut', BASE/'tools/public-serializer-extraction-kit/extract.py')
cut = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cut)
class Blob:
    def __init__(self, raw): self.raw = raw
    def read_bytes(self): return self.raw

# id, file, unique source anchor, shared by adopted tx1 and tx2, kind.
ITEMS = []
def add(file, shared, kind, rows):
    for name, anchor in rows:
        ITEMS.append((name, 'crates/aspis-r1-cost-probe/src/'+file+'.rs', anchor, shared, kind))
add('candidate', False, 'function', [
 ('candidate::tx2_authenticated','pub fn tx2_authenticated<'),
 ('candidate::tx2_common','fn tx2_common<')])
add('candidate', True, 'function', [
 ('candidate::parse_shape','pub fn parse_shape('), ('candidate::wide_view',"fn wide_view<'a>"),
 ('candidate::batch_merkle','fn batch_merkle<'), ('candidate::query_values','fn query_values('),
 ('candidate::opening','fn opening('), ('candidate::slot','fn slot(')])
add('verifier', False, 'function', [
 ('verifier::resume','pub fn resume<'), ('Reader::raw','fn raw<const N:'),
 ('Reader::e','fn e(&mut'), ('Reader::k','fn k(&mut'),
 ('verifier::finish_relation','pub fn finish_relation('), ('verifier::polynomial','pub fn polynomial(')])
add('verifier', True, 'function', [
 ('verifier::mark','fn mark('), ('verifier::checkpoint_size','pub fn checkpoint_size('),
 ('QueryGeometry::for_range','fn for_range('), ('QueryGeometry::for_query','fn for_query('),
 ('verifier::circle_fold_with_inverses','fn circle_fold_with_inverses('),
 ('verifier::line_fold_with_inverses','fn line_fold_with_inverses('),
 ('BatchedWeights::new','fn new(weights:'), ('BatchedWeights::push','fn push(&mut self,index:'),
 ('BatchedWeights::value','fn value(&self,index:'), ('BatchedWeights::finish','fn finish(&self,weights:'),
 ('verifier::accumulate_with_node','fn accumulate_with_node(')])
add('verifier', True, 'type', [
 ('verifier::Error','pub enum Error {'), ('verifier::Phase','pub enum Phase {'),
 ('verifier::Observer','pub type Observer='), ('verifier::View',"pub struct View<'a>"),
 ('verifier::Prepared','pub struct Prepared {'), ('verifier::Accumulator','pub struct Accumulator {'),
 ('verifier::QueryGeometry','struct QueryGeometry {'), ('verifier::BatchedWeights','struct BatchedWeights {')])
add('verifier', False, 'type', [('verifier::Reader',"struct Reader<'a>")])
add('verifier', True, 'global', [('verifier::CHECKPOINT_FIXED','pub const CHECKPOINT_FIXED:')])
add('multiproof', True, 'function', [
 ('multiproof::well_formed','fn well_formed('), ('multiproof::node_count','pub fn node_count('),
 ('multiproof::verify_in_place','pub fn verify_in_place<'),
 ('Arity::bits','pub const fn bits('), ('Arity::width','pub const fn width('), ('Arity::levels','pub const fn levels(')])
add('multiproof', True, 'type', [('multiproof::Arity','pub enum Arity {')])
add('multiproof', True, 'global', [(f'multiproof::{n}',f'pub const {n}:') for n in ['LEAF_BITS','BINARY_NODE_TAG','MAX_BATCH']])
# No expand/check/encode call is reachable from authenticated tx2. The layout
# constants include dependencies of the selected opening/view/slot offsets.
add('compact', True, 'global', [(f'compact::{n}',f'pub const {n}:') for n in [
 'MAGIC','HEADER','SPLIT','QUERIES','LOGICAL_SEMANTIC','SEMANTIC_COMPACT_VALUES',
 'COMPACT_SEMANTIC','COMPACT_Y1','OPENING','OFF_SEMANTIC','OFF_Y1','OFF_INACTIVE',
 'OFF_ROUND0','OFF_FOLDED_ROOT','OFF_ROUND1','OFF_FINAL','FINAL_LEN','OFF_OPENINGS',
 'OFF_NODES','FIXED','MAX_NODES','MAX_PROOF','SLOT_NODES','PROOF_BYTES']])
add('compact', True, 'function', [('compact::slot_offset','pub const fn slot_offset(')])
add('transport', True, 'type', [('transport::Variant','pub enum Variant {')])
add('transport', True, 'function', [(f'Variant::{n}',f'pub fn {n}(self)') for n in ['tag','folds','final_len']])
add('verifier', True, 'global', [('verifier::SEMANTIC_BYTES','pub const SEMANTIC_BYTES:')])
ITEMS.append(('adapter::stage2', 'programs/r1-cost-probe/src/r1_pool_adapter.rs',
              'fn stage2(', False, 'function'))
# Named transitive implementation boundaries: bodies are pinned, not extracted
# by this packet. Their recursive arithmetic/allocator/SDK cones stay explicit.
BACKENDS = {
 'weights.rs': ['powers','field','Weights::new','Weights::pair'],
 'fast_dots.rs': ['four_dots'],
 'fast_pairing.rs': ['EbyKDot::new','EbyKDot::push','EbyKDot::finish','canonical::reduce'],
 'fast_domain.rs': ['fibre_point','line_node'],
 'trace.rs': ['value (non-prover branch)'],
}
EXTERNALS = {
 'crates/aspis-core/src/digest.rs': ['Digest32::digest (generic H; caller supplies SolanaDigest)'],
 'crates/aspis-core/src/field.rs': ['M31/CM31/QM31/WideExact types, constants, strict byte decoders, arithmetic and equality'],
 'crates/aspis-core/src/field/wide_exact.rs': ['WideExact implementation behind field.rs'],
 'crates/aspis-core/src/circle.rs': ['SecureCirclePoint'],
 'crates/aspis-core/src/r0/domain.rs': ['FibreIndex::new'],
 'crates/aspis-core/src/r0/mod.rs': ['heap::filled and allocation error'],
 'crates/aspis-core/src/r0/merkle.rs': ['C1_TAG/C2_TAG, parent_with_digest (Arity::Eight syntactic branch)'],
 'crates/aspis-core/src/state_only_private_merkle.rs': ['private_leaf_hash_with_digest'],
 'programs/r1-cost-probe/src/r1_pool_adapter.rs': ['stage2, validate_asq8, emit_result; SDK/account custody and serializer boundary'],
 'programs/r1-cost-probe/src/lib.rs': ['SolanaDigest, observer, error'],
}
# Named source closures, including multiple occurrences of equal lambda text.
CLOSURES = {
 'candidate::parse_shape': ['|&x| x != 0'],
 'candidate::batch_merkle': ['|w| u64::from_le_bytes(w.try_into().unwrap()) != 0'],
 'candidate::query_values': ['|s| field(&q[672..800], s)'],
 'verifier::resume': ['|&b|b!=0', '|_|u32::from_le_bytes(r.raw())', '|_|Error::Allocation'],
 'QueryGeometry::for_range': ['|_|Error::Query', '|_|Error::Query', '|_|Error::Query', '|x|*x==M31::ZERO', '|i|core::array::from_fn(|j|flat_inverse[5*i+j])', '|j|flat_inverse[5*i+j]'],
 'BatchedWeights::new': ['|_|Error::Allocation'],
 'verifier::polynomial': ['|a,i|a.mul(x).add(field(bytes,i))'],
 'verifier::finish_relation': ['|_|Error::Parse'],
 'adapter::stage2': ['|_| ProgramError::InvalidInstructionData'],
}

def build():
    revision=git('rev-parse',REV).decode().strip()
    sources={}
    for _,p,_,_,_ in ITEMS: sources[p]=git('show',revision+':'+p)
    for f in BACKENDS: sources['crates/aspis-r1-cost-probe/src/'+f]=git('show',revision+':crates/aspis-r1-cost-probe/src/'+f)
    for p in EXTERNALS: sources[p]=git('show',revision+':'+p)
    for p,raw in sources.items():
        assert (ROOT/p).read_bytes()==raw, 'frozen source differs: '+p
    stage1=BASE/'tools/tx1-caller-extraction-kit/input-accumulator/source-pins.json'
    stage1_pins=json.loads(stage1.read_text())
    rows=[]; bodies={}
    for name,p,anchor,shared,kind in ITEMS:
        body,start,end,line,last=cut.find_item(Blob(sources[p]),anchor)
        assert sources[p][start:end]==body
        matches=[]
        for old in stage1_pins['cuts']:
            if old['path']!=p: continue
            oldbody=(stage1.parent/'fragments'/ (old['name']+'.rs')).read_bytes()
            assert sha(oldbody)==old['sha256']
            if oldbody==body: matches.append(old['name'])
        rows.append(dict(name=name,path=p,kind=kind,sha256=sha(body),start_byte=start,
          end_byte_exclusive=end,start_line=line,end_line_exclusive=last,
          shared_with_adopted_stage1=shared,accepted_tx1_exact_fragment_matches=matches))
        bodies[name]=body
    closures=[]
    for owner,expressions in CLOSURES.items():
        text=bodies[owner].decode();used=collections.Counter()
        for exp in expressions:
            occurrence=used[exp];used[exp]+=1
            matches=list(re.finditer(re.escape(exp),text));assert len(matches)>occurrence,(owner,exp)
            closures.append(dict(owner=owner,expression=exp,occurrence=occurrence+1,expression_sha256=sha(exp.encode()),
                shared_with_adopted_stage1=next(x['shared_with_adopted_stage1'] for x in rows if x['name']==owner)))
    # Check old failed exact roots against the frozen definitions, rather than
    # relying on the historical revision label or a signature-only match.
    predecessors=[
      ('finish-pinned-static','lean-candidates/current-stage2-extraction-frontier-20261019/root-finish-relation-extraction-v1-20261019',
       {'verifier::finish_relation':'finish_relation'}),
      ('caller-correct-opacity','lean-candidates/stage2-extraction-frontier-addendum-20261019/attempts/root-stage2-adopted-caller-v2-20261019',
       {'candidate::tx2_authenticated':'stage2_tx2_authenticated','candidate::tx2_common':'stage2_tx2_common'}),
      ('resume-correct-layout','lean-candidates/current-stage2-extraction-frontier-20261019/root-stage2-adopted-resume-v2-20261019',
       {'verifier::resume':'stage2_resume'})]
    continuity=[]; outputs={}
    for label,rel,roots in predecessors:
        parent=BASE/rel; pins=parent/'input/source-pins.json'; meta=json.loads(pins.read_text())
        libpath=parent/'input/lib.rs'
        oldlib=libpath.read_bytes() if libpath.is_file() else None
        if oldlib is not None: assert sha(oldlib)==meta['kit_files']['lib.rs']
        for name,fragment in roots.items():
            old=bodies[name]
            assert meta['kit_files']['fragments/'+fragment+'.rs']==sha(old),name
            if oldlib is not None: assert oldlib.count(old)==1,name
            origin=next(x['path'] for x in rows if x['name']==name)
            assert git('show',meta['revision']+':'+origin).count(old)==1,name
            continuity.append(dict(name=name,predecessor=str(parent.relative_to(ROOT)),fragment=fragment,
                sha256=sha(old),frozen_equal=True,retained_lib_checked=oldlib is not None))
        for phase in ['charon','aeneas']:
            r=parent/'runs'/(phase+'-a')/'receipt.json';receipt=json.loads(r.read_text())
            assert receipt['source_pins_sha256']==sha(pins.read_bytes())
            assert receipt['exit_status']==(0 if phase=='charon' else 2)
            outputs['receipts/'+label+'-'+phase+'.json']=r.read_bytes()
            for f in ['command.json','time.log','stdout-summary.json','stdout-excerpt.log','stdout-pin.json']:
                src=r.parent/f
                if src.is_file(): outputs['receipts/'+label+'-'+phase+'-'+f]=src.read_bytes()
    counts={'named_declarations':len(rows),'by_kind':dict(collections.Counter(x['kind'] for x in rows)),
      'shared_with_adopted_stage1':sum(x['shared_with_adopted_stage1'] for x in rows),
      'stage2_only':sum(not x['shared_with_adopted_stage1'] for x in rows),
      'exact_accepted_tx1_fragment_matches':sum(bool(x['accepted_tx1_exact_fragment_matches']) for x in rows),
      'source_closures':len(closures),
      'shared_closures':sum(x['shared_with_adopted_stage1'] for x in closures)}
    inventory=dict(schema='stage2-source-cut-inventory-v1',source_revision=revision,
      scope='Named orchestration declarations plus source closure inventory with explicit backend frontiers; NOT a full compiler-expanded/monomorphized cone cardinality.',
      counts=counts,declarations=rows,closures=closures,backend_frontiers=BACKENDS,external_frontiers=EXTERNALS,
      excluded=['candidate::canonical_scan (not called by authenticated path)','compact codec expansion/encoding/check_values (tx1 only)',
                'multiproof::generate/verify/sort_dedup/BinaryTree (not called)','retired eight_way and prover/test-only bodies'],
      stdlib_frontiers=['Option/Result and Try lowering','slice indexing/ranges, equality, contains, windows, swap, chunks_exact',
        'Iter/IterMut, Enumerate, Any/All, FromFn, Map/Collect, Rev/Fold, arrays and conversions',
        'Box/Vec allocation, deref/drop; function-pointer Observer Fn callback',
        'derive Clone/Copy/Debug/PartialEq/Eq implementations and integer checked operations'],
      stage1_comparison={'path':str(stage1.relative_to(ROOT)),'sha256':sha(stage1.read_bytes()),
        'note':'Shared means adopted source call reachability (both transactions), not prior Lean acceptance. Exact old tx1 fragment matches are separate; an absent match is not evidence of missing arithmetic proofs in other packets.'})
    outputs['pins/cone.json']=dump(inventory)
    outputs['pins/source-hashes.json']=dump({'source_revision':revision,'files':{p:{'sha256':sha(b),'bytes':len(b)} for p,b in sorted(sources.items())}})
    outputs['pins/predecessor-continuity.json']=dump(continuity)
    outputs['pins/required-tools.json']=dump({'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','charon-driver':'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45','aeneas-static-lean432':'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5',
      'historical_diagnostic_aeneas_only':'22232f96de983a1cdd4043a3fe2091b3ea4202fdec7a27789ad2612358fb62ae',
      'note':'The latter tool is historical diagnostic evidence, not a replacement for the required pinned binary. No tool ran in this packet.'})
    return outputs,counts

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    outputs,counts=build()
    for name,raw in outputs.items():
        p=OUT/name
        if a.check: assert p.read_bytes()==raw,name
        else: p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    print(json.dumps({'check':a.check,'counts':counts,'files':len(outputs),'no_builds':True},sort_keys=True))
if __name__=='__main__':main()
