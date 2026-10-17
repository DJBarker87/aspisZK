#!/usr/bin/env python3
"""Isolated diagnostic relocation of actual encoder/retention prefix."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 ref=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip();base=H/'input-build'
 pins=json.loads((base/'source-pins.json').read_text());outputs={n:(base/n).read_bytes() for n in pins['kit_files']}
 raw=subprocess.check_output(['git','-C',str(ROOT),'show',ref+':crates/aspis-r1-cost-probe/src/host_commitment.rs'])
 begin=raw.index(b'        let mut words = Vec::new();');end=raw.index(b'        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;',begin);prefix=raw[begin:end]
 lib=outputs['lib.rs'];assert lib.count(prefix)==1
 helper=(b'fn encode_and_retain_lanes(domain:&EncodingDomain,messages:&[Message<E>],variant:crate::transport::Variant,lanes:Vec<usize>)->Result<(Vec<usize>,Vec<Word>,Vec<Message<E>>),Error>{\n'+prefix+b'        Ok((lanes,words,saved))\n    }\n')
 replacement=b'        let (lanes,words,saved)=encode_and_retain_lanes(domain,messages,variant,lanes)?;\n'
 lib=lib.replace(prefix,replacement,1);assert lib.count(b'impl Commitment {')==1
 lib=lib.replace(b'impl Commitment {',helper+b'impl Commitment {',1)
 outputs['lib.rs']=lib
 pins.update(root_target='crate::host_commitment::encode_and_retain_lanes',namespace='AspisC2RetainedLanes',classification='UNADOPTED_DIAGNOSTIC_RETAINED_LANES_HELPER: exact encoder/reserve/retention prefix relocated; no production helper/build/caller acceptance')
 pins['kit_files']={n:sha(b) for n,b in outputs.items()}
 pins['diagnostic']={'source_revision':ref,'source_path':'crates/aspis-r1-cost-probe/src/host_commitment.rs','source_file_sha256':sha(raw),'prefix_start_byte':begin,'prefix_end_byte_exclusive':end,'prefix_sha256':sha(prefix),'helper_sha256':sha(helper),'parent_lib_sha256':sha((base/'lib.rs').read_bytes()),'adapted_lib_sha256':sha(lib),'mapping':'Exact words/saved reserves and for-loop bytes moved; lanes is owned input and returned unchanged before words/saved. Build replaces that exact prefix with helper call. No loop/body/coefficients/encoder rewrite. No production edit.','state_and_drop_obligations':'Preserve lanes-before-words-before-saved allocations; WrongField/encode error order; returned ownership; destructor/private-salt order must be checked before any adoption. No adoption claimed.','source_move_status':'NOT_ADOPTED_NOT_1F_QUALIFIED'}
 outputs['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'check':a.check,'lib_sha256':sha(lib),'pins_sha256':sha(outputs['source-pins.json']),'prefix_sha256':sha(prefix)}))
if __name__=='__main__':main()
