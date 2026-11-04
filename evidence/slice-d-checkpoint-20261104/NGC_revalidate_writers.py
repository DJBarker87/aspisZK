from pathlib import Path
import importlib.util,sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-field-20261104'
sys.path.insert(0,str(P))
spec=importlib.util.spec_from_file_location('NGC_NFT_certify',P/'NFT_certify.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
rows=[]
for p,n,copy,frame,root in [(6,7,(1,2),(16,17),'NFT_Bytes.cm_value'),(8,9,(3,4),(18,19),'NFT_Bytes.qm_value')]:
 m.pair(p,n);m.copy_pair(*copy);m.pair(*frame);rows.append(dict(native=[p,n],copy=list(copy),frame=list(frame),root=root))
audit=m.audit()
for row in rows:assert row['root']in audit
(E/'NGC_WRITERS_REVALIDATED.json').write_text(json.dumps(dict(status='PASS',packets=rows,source_validator_sha256=hashlib.sha256((P/'NFT_certify.py').read_bytes()).hexdigest(),fresh_kani_attempts=0,credit='REUSED; pending NGC combined replay and raw ax2 audit'),indent=1)+'\n')
print('PASS writer native/copy/frame pairs and historical raw audit, no rerun')
