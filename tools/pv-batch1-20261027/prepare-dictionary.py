"""Private alpha-renamed cohort for the pinned callback signatures, not a re-extraction."""
from pathlib import Path
import subprocess,hashlib,json,re,sys
E=Path('evidence/pv-batch1-20261027');O=E/'lean';rev='c57a344726745387efb38d1571d885c69ce829ee';base='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'
names={'ProverRwFullExternalTypes':'PV_B1_HostExternalTypes','ProverRwFullTypes':'PV_B1_HostTypes','ProverRwFullExternalFuns':'PV_B1_HostExternalFuns'};rows=[]
for old,new in names.items():
 path=base+old+'.lean';raw=subprocess.check_output(['git','show',rev+':'+path],text=True);s=raw
 for a,b in sorted(names.items(),key=lambda x:-len(x[0])):s=s.replace('R1Z.'+a,b)
 s=s.replace('ProverRwFull','PV_B1_Host')
 declarations=re.findall(r'^\s*(?:class|structure|inductive|def|abbrev) ([\w.]+)',s,re.M)
 queries='\n'.join('#print axioms '+n for n in declarations)
 assert s.count('end PV_B1_Host')==1
 s=s.replace('end PV_B1_Host',queries+'\nend PV_B1_Host')
 s='-- Private namespace/import rename of pinned callback signature source.\n'+s
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|\baxiom\s',s)
 p=O/(new+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
 rows.append(dict(module=new,source_path=path,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),private_sha256=hashlib.sha256(s.encode()).hexdigest(),queries=declarations))
manifest=dict(revision=rev,changes='Namespace/import renaming and axiom queries only; fields, quantifiers and signatures unchanged',rows=rows)
p=E/'dictionary-cohort.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print([(r['module'],len(r['queries'])) for r in rows])
