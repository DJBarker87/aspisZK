from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
P=Path('evidence/batch-merkle-20261108');E=Path(__file__).resolve().parent;sys.path.insert(0,str(P));import NJS_resolve as r
pins=[]
for n in ['NJS_NHR_stage.py','NJS_SUPPLEMENT.json','NJS_KMX.patch']:
 data=r.read(n);dest=n.replace('NJS','NKB')
 if n.endswith('.py'):data=data.replace(b'NHR_FROZEN',b'NKB_FROZEN').replace(b'NHR_STAGING',b'NKB_STAGING')
 (E/dest).write_bytes(data);pins.append(dict(source=str(P/n),destination=dest,sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
for n in ['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json']:
 p=Path('evidence/extract-stage-20261106')/n;data=p.read_bytes();dest=n.replace('NHR','NKB');(E/dest).write_bytes(data);pins.append(dict(source=str(p),destination=dest,sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
gate=(P/'NJS_gate.py').read_text().replace('NJS','NKB').replace('NHR_FROZEN','NKB_FROZEN')
a=gate.index('frag=');b=gate.index('h=(E/',a)
gate=gate[:a]+"frag=(E/'NKB_fragments.rs').read_bytes(); assoc=json.loads((E/'NKB_FRAGMENT_ASSOCIATION.json').read_text());\nfor item in assoc['spans']:\n body=item['body'];assert stage.sha(body.encode())==item['sha256'];assert body in raw.decode() and body in frag.decode()\n(S/'NKB_fragments.rs').write_bytes(frag)\n"+gate[b:]
(E/'NKB_gate.py').write_text(gate);(E/'NKB_PINNED_INPUTS.json').write_text(json.dumps(pins,indent=2)+'\n')
raw=Path('crates/aspis-r1-cost-probe/src/candidate.rs').read_text();a=raw.index('    let count = multiproof::node_count');b=raw.index('\n}\n',a);body=raw[a:b]
fragment='''// Exact frozen batch_tree terminal, exposed on arbitrary loop post-state.\nfn terminal_fragment<H:Digest32>(proof:&[u8],root:[u8;32],s:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,hash:H)->Result<(),Error>{\n'''+body+'\n}\n'
(E/'NKB_fragments.rs').write_text(fragment);(E/'NKB_FRAGMENT_ASSOCIATION.json').write_text(json.dumps(dict(spans=[dict(body=body,sha256=hashlib.sha256(body.encode()).hexdigest(),source='crates/aspis-r1-cost-probe/src/candidate.rs')]),indent=2)+'\n')
print('NKB terminal source and frozen inputs staged')
