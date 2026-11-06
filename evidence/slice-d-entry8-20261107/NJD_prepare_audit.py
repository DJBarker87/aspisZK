from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry7-20261107'
mods=['NJD_Trace','NJD_GuardCuts','NJD_EntrySpine','NJD_LaneStep','NJD_DigestLaw','NJD_Prefixes']
for m in ['ProofDriver','ScanDriver']:
 s=(P/('NIV_'+m+'.lean')).read_text().replace('NIV_','NJD_').replace('NIM_AUDIT_MODULES.json','NJD_AUDIT_MODULES.json');(E/('NJD_'+m+'.lean')).write_text(s)
(E/'NJD_audit_one.py').write_text((P/'NIV_audit_one.py').read_text().replace('NIV_','NJD_'))
ats=list(map(json.loads,(E/'NJD_ATTEMPTS.jsonl').read_text().splitlines()));roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest();rs=[r for r in ats if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert rs,m
 for line in rs[-1]['print_axioms']:
  root=re.match("'([^']+)'",line)[1]
  assert 'sorryAx' not in line and all(a in ['propext','Classical.choice','Quot.sound'] for a in re.findall(r'\[([^]]*)\]',line)[0].split(', ')) if '[' in line else True
  if root not in roots:roots.append(root)
(E/'NJD_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=1)+'\n')
lines={};diff=[]
for base in [P/'NIV_EXPECTED_IMPORTS.jsonl',E.parent/'ledger13-20261107/NIU_EXPECTED_IMPORTS.jsonl']:
 for x in map(json.loads,base.read_text().splitlines()):
  if x['module'] in lines and lines[x['module']]!=x:diff.append(dict(module=x['module'],old=lines[x['module']],new=x))
  lines[x['module']]=x
for m in mods+['NJD_COMBINED_IMPORT']:
 lines[m]=dict(module=m,imports=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M))
(E/'NJD_IMPORT_BASELINE_DIFFS.json').write_text(json.dumps(diff,indent=1)+'\n')
(E/'NJD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(lines[k])+'\n' for k in sorted(lines)))
print(json.dumps(dict(modules=len(mods),roots=len(roots),baseline_import_differences=len(diff))))
