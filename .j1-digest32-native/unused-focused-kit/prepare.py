#!/usr/bin/env python3
"""Verbatim migrated production cuts plus explicitly inventoried entry wrappers."""
from pathlib import Path
import argparse,hashlib,json,subprocess
HERE=Path(__file__).resolve().parent
REVISION='0ff133effe7ee299186700c2a91a35d5548b0ca5'
PATHS={'digest':'crates/aspis-core/src/digest.rs','wire':'crates/aspis-r1-cost-probe/src/r1_wire.rs'}
sha=lambda b:hashlib.sha256(b).hexdigest()
def expected():
 sources={name:subprocess.check_output(['git','show',REVISION+':'+path],cwd=HERE).decode() for name,path in PATHS.items()}
 cuts={};parts={}
 def cut(name,source,start,end=None):
  text=sources[source];a=text.index(start)
  if end is None:
   brace=text.index('{',a);depth=1;b=brace+1
   while depth:
    depth+=(text[b]=='{')-(text[b]=='}');b+=1
   if text[b:b+1]=='\n':b+=1
  else:b=text.index(end,a)
  parts[name]=text[a:b];cuts[name]={'source':PATHS[source],'start_line':text[:a].count('\n')+1,'end_line':text[:b].count('\n'),'sha256':sha(parts[name].encode()),'substitutions':[]}
 cut('trait','digest','pub trait Digest32: Copy {')
 cut('domain','wire','#[cfg(not(feature = "private-leaf-salts"))]','pub const LANES:')
 cut('error','wire','#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum Error {')
 cut('transcript','wire','#[derive(Clone)]\npub struct SemanticTranscript<H: Digest32> {')
 cut('new','wire','    pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32])')
 cut('state','wire','    pub fn state(&self) -> [u8; 32]')
 cut('next_row','wire','    pub fn next_row(&self) -> u8')
 cut('step','wire','    fn sample_block_validated(&mut self, row: u8, framed: &[u8])')
 header='impl<H: Digest32> SemanticTranscript<H> {\n';assert header in sources['wire']
 wrappers='''// Extraction entrypoints only: bodies are one call to the unchanged methods.
pub fn source_new<H: Digest32>(hash: H, public_bytes: &[u8], root: &[u8; 32]) -> Result<SemanticTranscript<H>, Error> {
    SemanticTranscript::new(hash, public_bytes, root)
}
pub fn source_step<H: Digest32>(transcript: &mut SemanticTranscript<H>, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
    transcript.sample_block_validated(row, framed)
}
pub fn source_inspect<H: Digest32>(transcript: &SemanticTranscript<H>) -> ([u8; 32], u8) {
    (transcript.state(), transcript.next_row())
}
'''
 lib='// Exact production declaration cuts. Only module scaffolding and root wrappers are kit-owned.\n#![no_std]\n#![allow(dead_code)]\nextern crate self as aspis_core;\npub use digest::Digest32;\npub mod digest {\n'+parts['trait']+'}\npub mod r1_wire {\nuse aspis_core::Digest32;\n'+''.join(parts[x]+'\n' for x in ['domain','error','transcript'])+header+''.join(parts[x] for x in ['new','state','next_row','step'])+'}\n'+wrappers+'}\n'
 outputs={'lib.rs':lib,'Cargo.toml':'[package]\nname = "aspis-r1-digest-source"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n\n[lib]\npath = "lib.rs"\n\n[features]\ndefault = []\nprivate-leaf-salts = []\n\n[workspace]\n','Cargo.lock':'version = 4\n\n[[package]]\nname = "aspis-r1-digest-source"\nversion = "0.0.0"\n'}
 for name,text in sources.items():outputs['original/'+name+'.rs']=text
 for name,text in parts.items():outputs['fragments/'+name+'.rs']=text
 pins={'classification':'Exact migrated production cuts; no Rust/compiler/syscall refinement claim','source_revision':REVISION,'sources':{PATHS[n]:sha(s.encode()) for n,s in sources.items()},'cuts':cuts,'impl_header_exact':header,'kit_wrappers':wrappers,'roots':['crate::r1_wire::source_new','crate::r1_wire::source_step','crate::r1_wire::source_inspect','crate::digest::Digest32'],'features':['private-leaf-salts'],'excluded':'Concrete SolanaDigest backend, SDK effects, other semantic/opening/caller bodies, Observer and field arithmetic','kit_files':{n:sha(t.encode()) for n,t in outputs.items()},'prepare_script_sha256':sha(Path(__file__).read_bytes())}
 outputs['source-pins.json']=json.dumps(pins,indent=2)+'\n';return outputs
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 for name,text in expected().items():
  dest=HERE/name
  if args.check:assert dest.read_bytes()==text.encode(),name
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text)
 print('PASS: eight verbatim production cuts, no body/signature substitutions; three explicit root wrappers')
