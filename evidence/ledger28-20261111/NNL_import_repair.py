from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;p=E/'NNL_EXPECTED_IMPORTS.jsonl';x={json.loads(l)['module']:json.loads(l)['imports']for l in p.read_text().splitlines()};rows=[json.loads(l)for l in(E/'NNL_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
for r in rows:
 if r['imports_match']:continue
 m=r['module'];assert m not in x,'Existing expected imports must not be inferred from loader'
 path='evidence/tx1-owned-20261111/'+('NMT_lean/'+m.replace('.','/')+'.lean'if'.'in m else m+'.lean')
 run=subprocess.run(['git','show','HEAD:'+path],capture_output=True)
 if run.returncode:
  path='evidence/tx1-owned-20261111/'+m+'.lean';run=subprocess.run(['git','show','HEAD:'+path],capture_output=True)
 assert run.returncode==0,(m,path)
 source=run.stdout;expected=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',source.decode(),re.M)));assert expected==r['imports'],(m,path,expected,r['imports'])
 x[m]=expected;pins.append(dict(module=m,source=path,sha256=hashlib.sha256(source).hexdigest(),imports=expected))
p.write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n'for k,v in sorted(x.items())))
(E/'NNL_IMPORT_REPAIR.json').write_text(json.dumps(dict(status='SOURCE_DERIVED_EXPECTED_IMPORTS',missing=len(pins),pins=pins,reason='New transitive NMT support dependencies were absent from job-owned expected inventory; never inferred from observed output alone',scan11_actual_exit=1,outer11_exit=0,outer11_bug='Vacuous collector-only exception accepted an empty scan root set; no scan credit',replacement='require proof mode, nonempty expected roots and at least one recognized collector disagreement; final scan at scope60 with corrected source-derived inventory'),indent=1)+'\n')
p=E/'NNL_batch.py';s=p.read_text().replace("collector_only=(r.returncode==1 and actual==expected", "collector_only=(name.startswith('proof') and bool(expected) and any(not z['equal']for z in x['results']) and r.returncode==1 and actual==expected");p.write_text(s)
p=E/'NNL_SCAN.json';old=json.loads(p.read_text());old.update(status='FAILED_IMPORT_INVENTORY_NO_CREDIT',exit_status=1,import_mismatches=len(pins));(E/'NNL_INITIAL_SCAN.json').write_text(json.dumps(old,indent=1)+'\n');p.write_text(json.dumps(dict(status='PENDING_FINAL_CORRECTED_SCAN',initial='NNL_INITIAL_SCAN.json',credit=False),indent=1)+'\n')
print('102 source-derived import entries; strict collector-only guard; scan pending')
