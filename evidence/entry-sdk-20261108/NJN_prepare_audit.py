from pathlib import Path
import json,re,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'entry-leaves-20261107'
mods=['NJN_GuardModel','NJN_AcquireLaws','NJN_DropLaws','NJN_CopyLaws','NJN_GuardComposition','NJN_RoundTrip','NJN_ClockModel','NJN_PdaModel','NJN_CopyInduction']
(E/'NJN_COMBINED_IMPORT.lean').write_text('import NJK_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
ats=list(map(json.loads,(E/'NJN_ATTEMPTS.jsonl').read_text().splitlines()));roots=['AspisR1.RPx_Deployed.deployed']
for m in mods:
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest();rs=[r for r in ats if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert rs,m
 for line in rs[-1]['print_axioms']:
  root=re.match("'([^']+)'",line)[1];assert 'sorryAx' not in line
  if root not in roots:roots.append(root)
(E/'NJN_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=1)+'\n')
lines={}
for line in (E.parent/'ledger14-20261108/NJK_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
 x=json.loads(line);lines[x['module']]=x
for m in mods+['NJN_COMBINED_IMPORT']:
 lines[m]=dict(module=m,imports=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M))
(E/'NJN_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(lines[k])+'\n' for k in sorted(lines)))
for n in ['ProofDriver','ScanDriver']:
 s=(P/f'NJH_{n}.lean').read_text().replace('NJH','NJN');(E/f'NJN_{n}.lean').write_text(s)
 (E/f'NJN_{n}.diff').write_text(''.join(difflib.unified_diff((P/f'NJH_{n}.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NJH_'+n+'.lean',tofile='NJN_'+n+'.lean')))
for n in ['audit_one','audit_stage']:
 s=(P/f'NJH_{n}.py').read_text().replace('NJH','NJN')
 if n=='audit_stage':s=s.replace("[(20,'NJN_ProofDriver'),(21,'NJN_ScanDriver')]","[(16,'NJN_ProofDriver'),(17,'NJN_ScanDriver')]").replace("[(22,'NJN_ProofDriver'),(23,'NJN_ScanDriver')]","[(18,'NJN_ProofDriver'),(19,'NJN_ScanDriver')]").replace("[(24,'fixtures','NJN_ProofDriver'),(25,'proof0','NJN_ProofDriver'),(26,'scan','NJN_ScanDriver')]","[(20,'fixtures','NJN_ProofDriver'),(21,'proof0','NJN_ProofDriver'),(22,'scan','NJN_ScanDriver')]")
 (E/f'NJN_{n}.py').write_text(s)
print(json.dumps(dict(modules=len(mods),roots=len(roots))))
