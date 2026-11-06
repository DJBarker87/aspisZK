from pathlib import Path
import json,hashlib,base64,lzma,difflib
B=Path(__file__).resolve().parent;S=B/'NJT_Q_src';p=S/'crates/aspis-core/src/r0_transcript.rs';t=p.read_text();start=t.index('fn block_rank(');end=t.index('\n/// Binary long division',start);body=t[start:end].strip();assert body.startswith('fn block_rank(')
ref='#[cfg(kani)]\n'+body.replace('fn block_rank(', 'fn NJT_Q_rank_ref(',1)+'\n'
attrs='#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(all(kani,not(NJT_Q_contract_invert)),kani::ensures(|out| *out == NJT_Q_rank_ref(block)))]\n#[cfg_attr(all(kani,NJT_Q_contract_invert),kani::ensures(|out| *out != NJT_Q_rank_ref(block)))]\n'
t=t[:start]+attrs+t[start:];t+='\n'+ref+'\n'+(B/'NJT_Q_contract.rs.txt').read_text();p.write_text(t);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'NJT_Q_SOURCE_PINS.json';pins=json.loads(f.read_text());pins['crates/aspis-core/src/r0_transcript.rs']=sha(p);f.write_text(json.dumps(pins))
payload=json.loads(lzma.decompress(Path('/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108/NJT_FROZEN_PAYLOAD.json.xz').read_bytes()));frozen=base64.b64decode(payload['crates/aspis-core/src/r0_transcript.rs']).decode();original=frozen[frozen.index('fn block_rank('):frozen.index('\n/// Binary long division',frozen.index('fn block_rank('))].strip();assert body==original;assert ref.split('\n',1)[1].replace('fn NJT_Q_rank_ref(','fn block_rank(',1).strip()==original
(B/'NJT_Q_RANK_REF.rs.txt').write_text(ref);(B/'NJT_Q_REF_IDENTITY.json').write_text(json.dumps(dict(reference_sha256=hashlib.sha256(ref.encode()).hexdigest(),normalized_body_sha256=hashlib.sha256(original.encode()).hexdigest(),identity='literal frozen block_rank body, identifier-only rename; retained emitted cohort association reused, no extraction',cargo_target_dir=str(B/'NJT_Q_target')),indent=2))
patch=''
for n in ['crates/aspis-core/src/lib.rs','crates/aspis-core/src/r0_transcript.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_Q_NATIVE.patch').write_text(patch);print('actual frozen rank contract and identical retained reference body installed')
