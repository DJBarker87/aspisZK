from pathlib import Path
import hashlib,json
B=Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015');W=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((W/'framing-selected-mask.json').read_text());out={}
for n,v in d.items():
 p=B/'attempts'/(v['attempt']+'-'+n.replace('.','_'));rp=p/'receipt.json';r=json.loads(rp.read_text());assert r['exit_status']==0
 src=Path(r['snapshot_path']);obj=Path(r['output_path']);assert sha(src)==r['source_sha256']==v['source_sha256'];assert sha(obj)==r['output_sha256']==v['object_sha256']
 for x in r['direct_imports']:assert sha(Path(x['object_path']))==x['object_sha256'],(n,x['module'])
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in r['axiom_reports'])
 out[n]={'source_snapshot':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'receipt':str(rp),'receipt_sha256':sha(rp),'direct_import_pins':r['direct_imports'],'axiom_reports':r['axiom_reports'],'exit_status':r['exit_status']}
print(json.dumps({'scope':'Read/hash verification of17 relevant live144 successful receipt/source/output/import records. No compilation.','modules':out,'focused_remaining_order':['FS2.LemmaA','FS2.Theorem','FS2.Duplex','FS2.DuplexDecode','R1TrailingStateFrame','R1PublicInitFrame','R1RecordFrameCodec']},indent=2,sort_keys=True))
