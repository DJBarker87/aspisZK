#!/usr/bin/env python3
"""Actual old/new query methods; explicit isolated native-only decoder/abort hooks."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
H=Path(__file__).resolve().parent;R=H.parents[1];BEFORE='deb68369b';SOURCE='crates/aspis-r1-cost-probe/src/transcript.rs';sha=lambda b:hashlib.sha256(b).hexdigest()
class Src:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
p=argparse.ArgumentParser();p.add_argument('--after',default='5a28a4b48');p.add_argument('--stage',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args();after=subprocess.check_output(['git','rev-parse',a.after],cwd=R,text=True).strip();get=lambda rev:subprocess.check_output(['git','show',rev+':'+SOURCE],cwd=R)
spec=importlib.util.spec_from_file_location('c',R/'docs/research/100bit-spend-path-20261013/tools/public-serializer-extraction-kit/extract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
old,new=get(BEFORE),get(after);old_method=c.find_item(Src(old),'pub fn queries(&mut self,')[0];new_method=c.find_item(Src(new),'pub fn queries(&mut self,')[0]
path=b'aspis_core::r0_transcript::queries_from_pairs';adapter=b'migration_queries_decode';assert new.count(path)==1 and old_method.count(path)==1
renamed=old_method.replace(b'pub fn queries(',b'pub fn migration_old_queries(',1).replace(path,adapter);cfg=b'#[cfg(all(test,feature="prover",feature="private-leaf-salts"))]'
wrapper=b'''\nfn migration_queries_decode(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{
 #[cfg(all(test,feature="prover",feature="private-leaf-salts"))] {return query_migration_tests::decode(blocks,advances);}
 #[cfg(not(all(test,feature="prover",feature="private-leaf-salts")))] {aspis_core::r0_transcript::queries_from_pairs(blocks,advances)}
}\n'''
overlay=new.replace(path,adapter)+wrapper+cfg+b'\nimpl<H:Digest32> Transcript<H>{\n'+renamed+b'\n}\n'+cfg+b'\n#[path="query_migration_tests.rs"] mod query_migration_tests;\n';files={SOURCE:overlay,'crates/aspis-r1-cost-probe/src/query_migration_tests.rs':(H/'harness.rs').read_bytes(),'crates/aspis-r1-cost-probe/src/query_migration_context.json':(H/'saved-s2-query-context.json').read_bytes()};pins={'before':subprocess.check_output(['git','rev-parse',BEFORE],cwd=R,text=True).strip(),'after':after,'old_method_sha256':sha(old_method),'new_method_sha256':sha(new_method),'production_source_sha256':sha(new),'overlay_files':{n:sha(b)for n,b in files.items()},'generator_sha256':sha(Path(__file__).read_bytes()),'context_sha256':sha((H/'saved-s2-query-context.json').read_bytes()),'adapters':'Wholeold method only renamed +same decoderidentifier replacement in bothold/new. Actualnew queries invoked on actualTranscript receiver; actualabsorb/coredecoder/fieldembedding/provertrace. DecoderErr testonly; DigestAbort paniccut explicitlynotProgramError; alteredoutput actualSHA exceptonebit inselectedanswer. SavedS2state/payload/17expectedcalls pinned from actual583orderedtrace; syntheticS1/D are controlcontexts,notvalidproofs.'};raw=(json.dumps(pins,indent=2)+'\n').encode()
if a.check:assert(H/'source-pins.json').read_bytes()==raw
else:(H/'source-pins.json').write_bytes(raw)
if a.stage:
 assert a.stage.resolve()!=R
 for name,b in files.items():
  q=a.stage/name;q.parent.mkdir(parents=True,exist_ok=True)
  if name==SOURCE:assert sha(q.read_bytes())in[pins['production_source_sha256'],pins['overlay_files'][SOURCE]]
  q.write_bytes(b)
 (a.stage/'query-migration-overlay.json').write_bytes(raw)
print(json.dumps({'status':'PASS','checked':a.check,'staged':str(a.stage)if a.stage else None,'after':after,'pins_sha256':sha(raw)}))
