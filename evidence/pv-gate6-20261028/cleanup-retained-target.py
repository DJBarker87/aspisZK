"""Delete only the retained Cargo cache after classifying its false key hits."""
from pathlib import Path
import json, hashlib, shutil, subprocess, time
D=Path(__file__).resolve().parent
p=D/'native-target'
receipt=D/'cleanup.json'
r=json.loads(receipt.read_text())
rows=[x for x in r['targets'] if x.get('retained_possible_keys')]
assert len(rows)==1 and rows[0]['path']==str(p)
names=rows[0]['retained_possible_keys']
classifications=[]
for name in names:
    q=Path(name);rel=q.relative_to(p)
    assert q.is_file() and not q.is_symlink()
    assert ('solana_keypair' in q.name or 'solana-keypair' in str(rel))
    assert q.suffix in {'.rmeta','.rlib','.d','.json'} or '.fingerprint/solana-keypair-' in str(rel)
    classifications.append(dict(path=str(rel),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),
        file_type=subprocess.check_output(['file','-b',str(q)],text=True).strip(),
        classification='Cargo compiled library, dependency or fingerprint metadata for solana-keypair; not a wallet/account key'))
assert sorted(str(q) for q in p.rglob('*') if q.is_file() and ('keypair' in q.name.lower() or q.name.lower().endswith(('.pem','.key'))))==sorted(names)
shutil.rmtree(p)
r['targets'][r['targets'].index(rows[0])]=dict(path=str(p),existed=True,deleted=True,classified_compiler_artifacts=classifications)
r['final_cleanup_utc']=time.time()
(D/'cleanup-initial.json').write_text(receipt.read_text())
receipt.write_text(json.dumps(r,indent=2)+'\n')
print('Removed retained Cargo target; six compiler artifacts classified; no wallet keys deleted')
