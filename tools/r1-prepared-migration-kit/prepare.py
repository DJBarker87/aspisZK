#!/usr/bin/env python3
"""Exact approved Prepared source gate: native-only synthetic interface failures."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BEFORE='3da1531fc';AFTER='96aad8ef209cb69d7667ab5d8728bd4584a86d16'
SOURCE='crates/aspis-r1-cost-probe/src/verifier.rs'
sha=lambda b:hashlib.sha256(b).hexdigest()
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b

def build():
 cutter=ROOT/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py';spec=importlib.util.spec_from_file_location('c',cutter);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
 get=lambda rev,path:subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+path])
 old,new=get(BEFORE,SOURCE),get(AFTER,SOURCE)
 before=c.find_item(Source(old),'#[inline(never)]\n    pub fn new<H:Digest32>')[0]
 after=c.find_item(Source(new),'#[inline(never)]\n    pub fn new<H:Digest32>')[0]
 renamed=before.replace(b'pub fn new<H:Digest32>',b'pub fn migration_old_new<H:Digest32>',1);assert renamed!=before
 cfg='#[cfg(all(test, feature="prover", feature="private-leaf-salts"))]'
 verifier=new+b'\n'+cfg.encode()+b'\nimpl Prepared {\n'+renamed+b'\n}\n'+cfg.encode()+b'\n#[path="prepared_migration_tests.rs"]\npub(crate) mod prepared_migration_tests;\n'
 fp='crates/aspis-r1-cost-probe/src/fast_pairing.rs';trans='crates/aspis-r1-cost-probe/src/transcript.rs'
 pair=get(AFTER,fp);anchor=b'    pub fn push(&mut self, value: E, scalar: QM31) -> Result<(), ()> {';assert pair.count(anchor)==1
 pair_overlay=pair.replace(anchor,anchor+b'\n        '+cfg.encode()+b'\n        if crate::verifier::prepared_migration_tests::before_push(value,scalar) { return Err(()); }',1)
 transcript=get(AFTER,trans);anchor=b'        let (q,state)=aspis_core::r0_transcript::queries_from_pairs';assert transcript.count(anchor)==1
 trans_overlay=transcript.replace(anchor,b'        '+cfg.encode()+b'\n        if crate::verifier::prepared_migration_tests::before_queries() { return Err(crate::verifier::Error::Transcript); }\n'+anchor,1)
 files={SOURCE:verifier,fp:pair_overlay,trans:trans_overlay,'crates/aspis-r1-cost-probe/src/prepared_migration_tests.rs':(HERE/'harness.rs').read_bytes()}
 pins={'before_revision':subprocess.check_output(['git','rev-parse',BEFORE],cwd=ROOT,text=True).strip(),'after_revision':AFTER,'exact_old_prepared_new_sha256':sha(before),'exact_new_prepared_new_sha256':sha(after),'sole_old_body_adapter':'Rename method new to migration_old_new; whole method bytes otherwise retained.','production_files':{p:sha(get(AFTER,p)) for p in [SOURCE,fp,trans]},'overlay_files':{p:sha(b) for p,b in files.items()},'generator_sha256':sha(Path(__file__).read_bytes()),'harness_sha256':sha((HERE/'harness.rs').read_bytes()),'scope':'Test-only overlay in an isolated native source snapshot. Real field arithmetic, actual old/new whole Prepared bodies, recording SHA and actual trace::value. Synthetic failure at each174 EbyKDot::push position, post-eight-hash-pairs query-sampler boundary failure, and success for S1/S2/D. These configured interface failures are not claimed production-reachable. No production file is changed by generation.'}
 return files,pins

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--stage',type=Path);a=ap.parse_args();files,pins=build();p=HERE/'source-pins.json';raw=(json.dumps(pins,indent=2)+'\n').encode()
 if a.check:assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 if a.stage:
  source=a.stage.resolve();assert source!=ROOT and source.is_dir()
  for name,b in files.items():
   dest=source/name
   if name in pins['production_files']:assert sha(dest.read_bytes()) in [pins['production_files'][name],pins['overlay_files'][name]],name
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  (source/'prepared-migration-overlay.json').write_bytes(raw)
 print(json.dumps({'status':'PASS','checked':a.check,'staged':str(a.stage) if a.stage else None,'overlay_files':len(files),'source_pins_sha256':sha(raw)}))
if __name__=='__main__':main()
