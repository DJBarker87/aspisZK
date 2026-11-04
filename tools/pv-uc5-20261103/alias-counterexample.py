"""Finite counterexample for the superseded 29f011ca client's numeric FD check."""
from pathlib import Path
import json,os,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');B=H/'native-target/client/user_client'
assert hashlib.sha256(B.read_bytes()).hexdigest()=='29f011caab3501bf0525ada1727097f4b6263b92189ffa220eb61954571d98d9'
F=json.loads((H/'fixture-inputs.json').read_text());record=bytes.fromhex(F['records'][0]);q=json.loads((H.parent/'codex-pv-c474-20261029/runtime-private-final/default/transfer/request.json').read_text());q.pop('note');q.update(lane_leaf_sets=F['lane_leaf_sets'],withdrawal_amount=250,proof_dir=str(H/'final-gates/uc5/alias-private-retained'))
r,w=os.pipe();os.write(w,record);os.close(w);outread,outwrite=os.pipe();alias=os.dup(outwrite);q.update(wallet_bytes_fd=r,wallet_output_fd=alias)
p=subprocess.Popen([str(B)],stdin=subprocess.PIPE,stdout=outwrite,stderr=subprocess.PIPE,pass_fds=(r,alias));os.close(r);os.close(outwrite);os.close(alias)
p.stdin.write(json.dumps(q).encode());p.stdin.close();prefix=b''
while len(prefix)<212:
 block=os.read(outread,212-len(prefix))
 if not block:break
 prefix+=block
os.close(outread)
if p.poll() is None:p.terminate()
p.wait(timeout=30);stderr=p.stderr.read()
assert prefix==record,'expected alias counterexample not observed'
row=dict(evidence_class='finite native checked counterexample for superseded client',binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),output_fd_greater_than2=True,output_descriptor_number_distinct=True,underlying_pipe_aliases_stdout=True,secret_record_emitted_on_stdout=True,matched_prefix_bytes=212,secret_bytes_persisted_by_harness=False,process_exit=p.returncode,stderr_bytes=len(stderr),source_repair='0e3df6e684 compares device/inode with stdio and input before witness read')
(H/'final-gates/uc5/alias-counterexample.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
