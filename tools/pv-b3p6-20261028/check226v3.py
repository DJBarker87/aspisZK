"""Fail-closed shape preflight for the smaller owned reference; no link credit."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-b3p6-20261028'
p=R/'tools/pv-b3p6-20261028/reference226.rs';s=p.read_text()
chunk8=s.split('fn chunk8(',1)[1].split('fn chunk(',1)[0]
assert list(map(int,re.findall(r'byte_at\(p, base \+ (\d+)\)\?',chunk8)))==list(range(8))
chunk=s.split('fn chunk(',1)[1].split('pub fn encode_owned',1)[0]
assert list(map(int,re.findall(r'chunk8\(p, base \+ (\d+)\)\?',chunk)))==list(range(0,64,8))
assert re.findall(r'a(\d+)\[(\d+)\]',chunk)==[(str(a),str(b)) for a in range(8) for b in range(8)]
encode=s.split('pub fn encode_owned',1)[1].split('pub fn project',1)[0]
assert list(map(int,re.findall(r'chunk\(p, (\d+)\)\?',encode)))==list(range(0,1472,64))
project=s.split('pub fn project(',1)[1].split('pub fn public_bytes',1)[0]
assert 'let mut' not in project and 'project_frontier_level' not in s
for field,value in [('next_pair_index','transition.live_snapshot.next_pair_index'),('frontier','transition.live_snapshot.frontier'),('next_root','transition.candidate_afterstate.next_root'),('next_frontier','transition.candidate_afterstate.next_frontier')]:
 assert field+': '+value in project
assert 'pub anchor: [M31; 8]' in s and 'pub asset_id: M31' in s
assert 'if i >= n { return Ok(0); }' in s
record={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'reference_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'subchunk_bytes':8,'subchunks_per_chunk':8,'chunks':23,'padded_capacity':1472,'transfer_bytes':1455,'withdrawal_bytes':1427,'projection_mutable_writes':0,'body_is_reference_only':True,'native_link_credit':False,'note':'shape validation only; extraction, complete-Result laws, native correspondence and finite emission validation are separate gates'}
(D/'preflight226v3.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
