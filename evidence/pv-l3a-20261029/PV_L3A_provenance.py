from pathlib import Path
import subprocess,json,hashlib,re
D=Path(__file__).resolve().parent
rev='42760700cbae39587de93f520aed51618e13ef0a'
def gitfile(p):return subprocess.check_output(['git','show',rev+':'+p])
manifest=json.loads(gitfile('evidence/pv-rdea-20261028/build-source-pins.json'))
extra=json.loads(gitfile('evidence/pv-rdea-20261028/additional-build-inputs-expected.json'))
rows=[];sources={}
for r in manifest['files']+extra:
    p=r['path']
    try:s=gitfile(p)
    except subprocess.CalledProcessError:s=None
    actual=hashlib.sha256(s).hexdigest() if s is not None else None
    rows.append(dict(path=p,expected=r['sha256'],actual=actual,matches=actual==r['sha256']))
    if s is not None and p.endswith('.rs'):sources[p]=s.decode()
inv=[]
for p,s in sources.items():
    for n,line in enumerate(s.splitlines(),1):
        if re.search(r'\.\s*(?:try_inv|inv)\s*\(',line):inv.append(dict(path=p,line=n,text=line.strip(),classification='source candidate; cfg/test/reachability not inferred by regex'))
(D/'source-parity.json').write_text(json.dumps(dict(current_revision=rev,cached_build_revision=manifest['revision'],checks=rows,all_match=all(r['matches'] for r in rows),note='Complete listed-file byte comparison, not compiler-preservation or full dependency closure proof'),indent=2)+'\n')
(D/'source-inversion-candidates.json').write_text(json.dumps(inv,indent=2)+'\n')
# Retain build/config evidence locally without copying any binary.
for p in ['client-artifact.json','build-command.json','build04-time.log','additional-build-inputs-check.json']:
    (D/('reused-'+p)).write_bytes(gitfile('evidence/pv-rdea-20261028/'+p))
# Metadata supplied by the deployed library/source audit.
p='evidence/pv-l2d-20261028/deployed-client-features.json';(D/'reused-deployed-client-features.json').write_bytes(gitfile(p))
print(json.dumps(dict(checked=len(rows),missing=sum(r['actual'] is None for r in rows),mismatches=[r['path'] for r in rows if not r['matches']],source_inverse_candidates=len(inv))))
