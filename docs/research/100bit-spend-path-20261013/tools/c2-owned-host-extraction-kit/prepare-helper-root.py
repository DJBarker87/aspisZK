#!/usr/bin/env python3
"""Retarget preserved unchanged-loop helper diagnostic; no production edit."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 rev=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip()
 arc=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-followup-diagnostics-20261017/followup-diagnostics.tar.gz'
 assert sha(arc.read_bytes())=='5ff6e4ea749b7e13c035209495bc4ab8526e3b468473880a1102cbb22f788b5b'
 with tarfile.open(arc) as tf:
  outputs={m.name[len('copy-helper/input/'):]:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile() and m.name.startswith('copy-helper/input/')}
 pins=json.loads(outputs['source-pins.json']);oldpins=sha(outputs['source-pins.json']);lib=outputs['lib.rs']
 assert sha(lib)==pins['diagnostic']['adapted_lib_sha256']
 raw=subprocess.check_output(['git','-C',str(ROOT),'show',rev+':crates/aspis-r1-cost-probe/src/prover.rs'])
 loop=b'for (i,c) in columns.into_iter().enumerate(){self.messages[26+i]=c.map(E::from_qm31);}'
 assert raw.count(loop)==1
 helper=b'fn copy_c2_columns(messages:&mut Vec<Message<E>>,columns:[&[K;1024];2]) {'+loop.replace(b'self.messages',b'messages')+b'}'
 assert lib.count(helper)==1
 pins.update(root_target='crate::prover::copy_c2_columns',namespace='AspisC2CopyColumns',classification='UNADOPTED_DIAGNOSTIC_HELPER_ONLY: exact original loop moved with only self.messages to messages substitution; no production helper/caller acceptance')
 pins['diagnostic'].update(root_scope='Only private helper, excluding Backend caller/carrier and constructor',parent_archive_sha256=sha(arc.read_bytes()),parent_input_pins_sha256=oldpins,original_source_revision=rev,original_file_sha256=sha(raw),original_loop_sha256=sha(loop),helper_sha256=sha(helper),source_move_status='NOT_ADOPTED_NOT_1F_QUALIFIED')
 outputs['source-pins.json']=(json.dumps(pins,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'check':a.check,'lib_sha256':sha(lib),'pins_sha256':sha(outputs['source-pins.json']),'target':pins['root_target']}))
if __name__=='__main__':main()
