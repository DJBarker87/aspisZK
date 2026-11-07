from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
row=next(r for r in json.loads((E/'PCI_SOURCE_MAP.json').read_text()) if r['id']=='POOL:279')
frozen=row['frozen_function'];body=frozen[frozen.index('        let slot'):frozen.index('\n    }\n    let filled')]
s=(E/'PCI_AppendWindow.rs').read_text();copy=s[s.index(' let slot='):s.index('\n start\n}')]
copy=copy.replace('usize::from(filled)','usize::from(header.filled)').replace('data[0..32]','data[start..start+32]')
norm=lambda s:re.sub(r'\s+','',s)
assert norm(body)==norm(copy)
assert norm(copy.replace('*32','*31',1))!=norm(body)
assert norm(copy.replace('encode_digest_canonical(root)','encode_digest_canonical(&[aspis_core::field::M31::ZERO;8])'))!=norm(body)
r=dict(row='POOL:279',scope='one loop body only; no whole-row credit',frozen_function_sha256=row['full_function_sha256'],fission_sha256=hashlib.sha256((E/'PCI_AppendWindow.rs').read_bytes()).hexdigest(),body_exact_after_whitespace=True,transforms=['header.filled projected to filled','mutable32-byte range projected to valid32-byte owned window','start returned as auxiliary observation'],classification='ReviewedTranscription option A',controls=['wrong stride rejected','wrong encoder argument rejected'],missing='native arbitrary iterator association and complete count/frame composition')
p=E/'PCI_ASSOCIATIONS.json';records=[v for v in json.loads(p.read_text()) if v.get('row')!='POOL:279'];p.write_text(json.dumps(records+[r],indent=1)+'\n')
print('PCI279 loop-window diff and mutation controls pass')
