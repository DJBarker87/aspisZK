#!/usr/bin/env python3
"""Source-only exact tx1 differential kit and isolated cfg(test) injection overlay."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BEFORE='3335eecf2f2a08096abe95c67ac6b304f2df6284'
AFTER='96aad8ef209cb69d7667ab5d8728bd4584a86d16'
SOURCE='crates/aspis-r1-cost-probe/src/verifier.rs'
sha=lambda b:hashlib.sha256(b).hexdigest()
CFG='#[cfg(all(test, feature="prover", feature="private-leaf-salts"))]'

def git(rev,path):return subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+path])
def item(raw,anchor):
 spec=importlib.util.spec_from_file_location('lex',ROOT/'docs/research/100bit-spend-path-20261013/tools/j1e-source-effect-audit.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 body,_,_,_,_=m.fragment(raw,anchor)
 return body.encode()
def checkpoint_wrap(raw):
 old=b'let bytes=checkpoint(&p,&a,proof,public_bytes,hash);'
 new=b'let bytes=crate::verifier::tx1_migration_tests::checkpoint_result(&p,&a,proof,public_bytes,hash)?;'
 assert raw.count(old)==1
 return raw.replace(old,new,1)
def shared_checkpoint_wrap(raw):
 old=b'let bytes=checkpoint(&p,&a,proof,public_bytes,hash);'
 new=b'let bytes=checkpoint_result(&p,&a,proof,public_bytes,hash)?;'
 assert raw.count(old)==1
 return raw.replace(old,new,1)
def prepare(base=None):
 old,new=git(BEFORE,SOURCE),git(AFTER,SOURCE)
 old_tx=item(old,'pub fn tx1<H:Digest32>');new_tx=item(new,'pub fn tx1<H:Digest32>');finish=item(new,'fn tx1_finish<H:Digest32>')
 # The baseline method is complete; only the free-function name is adapted.
 renamed=old_tx.replace(b'pub fn tx1<H:Digest32>',b'pub fn migration_old_tx1<H:Digest32>',1);assert renamed!=old_tx
 source=new if base is None else base
 assert source.startswith(new),'An explicitly pinned prior overlay must retain the final production source as a byte prefix'
 # Result wrapper is symmetric: old full tx1 and new tail checkpoint call.
 assert source.count(finish)==1
 replacement=checkpoint_wrap(finish)
 source=source.replace(finish,replacement,1)
 geometry=b'    fn for_range(queries:&[u32;22],start:usize,end:usize)->Result<Self,Error> {'
 assert source.count(geometry)==1
 source=source.replace(geometry,geometry+b'\n        '+CFG.encode()+b'\n        if tx1_migration_tests::before_geometry(queries,start,end) { return Err(Error::Query); }',1)
 query=b'fn query_with_geometry<H:Digest32>(v:&View<\'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry)->Result<(),Error> {'
 assert source.count(query)==1
 source=source.replace(query,query+b'\n    '+CFG.encode()+b'\n    if tx1_migration_tests::before_query(p,a) { return Err(Error::Query); }',1)
 # Only test builds use the Result checkpoint adapter; native non-test gates
 # must retain the exact production expression in tx1_finish.
 source=source.replace(replacement,finish.replace(b'let bytes=checkpoint(&p,&a,proof,public_bytes,hash);',
   b'let bytes={\n        '+CFG.encode()+b'\n        { crate::verifier::tx1_migration_tests::checkpoint_result(&p,&a,proof,public_bytes,hash)? }\n        #[cfg(not(all(test, feature="prover", feature="private-leaf-salts")))]\n        { checkpoint(&p,&a,proof,public_bytes,hash) }\n    };'),1)
 source+=b'\n'+CFG.encode()+b'\n'+checkpoint_wrap(renamed)+b'\n'+CFG.encode()+b'\n#[path="tx1_migration_tests.rs"]\npub(crate) mod tx1_migration_tests;\n'
 actual_files={SOURCE:source,'crates/aspis-r1-cost-probe/src/tx1_migration_tests.rs':(HERE/'real-fixture.rs').read_bytes()}
 shared_old=b'use super::shared::*;\n'+shared_checkpoint_wrap(old_tx)+b'\n'
 shared_new=b'use super::shared::*;\n'+shared_checkpoint_wrap(finish)+b'\n'+new_tx+b'\n'
 pins={'before_revision':BEFORE,'after_revision':AFTER,'production_verifier_sha256':sha(new),
  'exact_old_tx1_sha256':sha(old_tx),'exact_new_tx1_sha256':sha(new_tx),'exact_new_tx1_finish_sha256':sha(finish),
  'actual_overlay_files':{p:sha(b) for p,b in actual_files.items()},
  'shared_exact_body_files':{'shared/old.rs':sha(shared_old),'shared/new.rs':sha(shared_new)},
  'generator_sha256':sha(Path(__file__).read_bytes()),'real_harness_sha256':sha((HERE/'real-fixture.rs').read_bytes()),'shared_harness_sha256':sha((HERE/'shared-harness.rs').read_bytes()),
  'transformations':['Old free function tx1 renamed migration_old_tx1 in actual crate overlay only; entire body otherwise retained except the symmetric checkpoint Result wrapper.',
  'The infallible checkpoint call in old tx1/new tx1_finish is symmetrically wrapped as checkpoint_result(...)? for test-only synthetic Err(Checkpoint); non-test final tx1_finish retains the exact original checkpoint expression.',
  'cfg(test,prover,private-leaf-salts) geometry entry hook may return Error::Query before setup; query_with_geometry entry hook may return Error::Query before first query0 or last query21.',
  'Shared-interface old/new modules preserve complete source bodies except identical checkpoint Result-call wrapping; their names remain tx1 in separate modules. All dependencies are explicit common synthetic interfaces, not production execution.'],
  'shared_interface_limits':{'field':'E = u64, not WideExact; arithmetic and all parse/semantic/prepare/geometry/query/checkpoint implementations are shared synthetic interfaces',
  'digest':'Deterministic recorded byte recurrence, explicitly not SHA or the production sampler',
  'purpose':'Exact Rust control-flow, Result propagation, call/state/trace/observer/digest-prefix comparison for S1/S2/D in both observer modes only; no production proof acceptance or field equivalence claim'},
  'fixture_files':{p:{'sha256':sha(git(AFTER,p)),'bytes':len(git(AFTER,p))} for p in [
  'docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin',
  'docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin']},
  'coverage':{'k':22,'first_query':0,'last_query':21,'actual_saved_fixture':'S2 P3 full tx1, real SHA, fields, semantic verification, query bodies and checkpoint; failures themselves synthetic','shared_interface_variants':['S1','S2','D'],'cases_per_variant':['success','geometry','query0','query21','checkpoint'],'observer_features':'real gate enables detail-phases; shared harness explicitly models both default and detailed observer modes'},
  'scope':'No production edit or proof generation. Generator emits source only. A runs capped optimized native gates; synthetic failures are never claimed production-reachable.'}
 return actual_files,{'shared/old.rs':shared_old,'shared/new.rs':shared_new},pins

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--stage',type=Path);ap.add_argument('--base-overlay-pins',type=Path);a=ap.parse_args()
 files,shared,pins=prepare();raw=(json.dumps(pins,indent=2)+'\n').encode()
 for name,b in shared.items():
  p=HERE/name
  if a.check:assert p.read_bytes()==b,name
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 p=HERE/'source-pins.json'
 if a.check:assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 if a.stage:
  assert a.stage.resolve()!=ROOT and a.stage.is_dir()
  current=(a.stage/SOURCE).read_bytes();base_pin=None
  if sha(current)!=pins['production_verifier_sha256']:
   assert a.base_overlay_pins,'Nonproduction stage requires explicit prior overlay pins'
   base_raw=a.base_overlay_pins.read_bytes();base_pin=json.loads(base_raw)
   assert base_pin['after_revision']==AFTER and sha(current)==base_pin['overlay_files'][SOURCE]
   files,_,composite=prepare(current);composite['base_overlay_pins_sha256']=sha(base_raw)
  else:composite=pins
  for name,b in files.items():
   dest=a.stage/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  (a.stage/'tx1-migration-overlay.json').write_text(json.dumps(composite,indent=2)+'\n')
 print(json.dumps({'status':'PASS','checked':a.check,'staged':str(a.stage) if a.stage else None,'source_pins_sha256':sha(raw)}))
if __name__=='__main__':main()
