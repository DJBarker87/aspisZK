"""Serializer structural preflight; incomplete obligations are explicit."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-b3p6-20261028'
P=R/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
s=P.read_text();body=s.split('pub fn public_bytes(self)',1)[1].split('/// Fast K path.',1)[0]
sequence=['let p = self.semantic();','let mut out = Vec::new();','out.push(match p.variant',
 'fields(&mut out, &p.anchor)?;','fields(&mut out, &p.nullifier)?;','fields(&mut out, &[p.asset_id])?;',
 'out.push(u8::from(p.recipient.is_some()));','if let Some(value) = p.recipient',
 'fields(&mut out, &value)?;','fields(&mut out, &p.change)?;',
 'out.push(u8::from(p.withdrawal_amount.is_some()));','if let Some(value) = p.withdrawal_amount',
 'fields(&mut out, &[M31(value)])?;','let source = p.transition.live_snapshot;',
 'let after = p.transition.candidate_afterstate;',
 'out.extend_from_slice(&source.next_pair_index.to_le_bytes());',
 'frontier(&mut out, &source.frontier)?;','fields(&mut out, &after.next_root)?;',
 'frontier(&mut out, &after.next_frontier)?;','Ok(out)']
pos=-1
for item in sequence:pos=body.index(item,pos+1)
assert re.findall(r'fields\(out, &values\[(\d+)\]\)\?;',body)==list(map(str,range(20)))
assert 'if value.0 >= aspis_core::field::P' in body
assert 'out.extend_from_slice(&value.0.to_le_bytes());' in body
ref=R/'tools/pv-b3p6-20261028/reference226.rs';r=ref.read_text()
chunk=r.split('fn chunk(',1)[1].split('pub fn encode_owned',1)[0]
assert list(map(int,re.findall(r'byte_at\(p, base \+ (\d+)\)\?',chunk)))==list(range(64))
encode=r.split('pub fn encode_owned',1)[1].split('pub fn project',1)[0]
assert list(map(int,re.findall(r'chunk\(p, (\d+)\)\?',encode)))==list(range(0,1472,64))
assert 'if i >= n { return Ok(0); }' in r
record={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'shipped_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),
 'reference_sha256':hashlib.sha256(ref.read_bytes()).hexdigest(),
 'native_declaration_order':sequence,'frontier_levels':20,'chunk_width':64,'chunk_count':23,
 'lengths':{'transfer':1455,'withdrawal':1427},'padding_end':1472,
 'binding_complete':False,'evidence_class':'structural preflight only; no native-link credit',
 'unproved_differences':[
 'native field check once versus reference check per byte: needs checked complete_word',
 'native little-endian byte expansion versus wrapping shifts and casts',
 'native append traversal versus indexed byte_at: needs every region and bound',
 'reference projection writes versus native SemanticPublic projection',
 '64-byte grouping and23 chunks versus append order: needs complete Result composition',
 'padding/truncation and complete successful non-vacuity witness',
 'same-input emitted/native differential for all projection writes remains pending']}
(D/'preflight226.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['binding_complete','evidence_class','lengths']}))
