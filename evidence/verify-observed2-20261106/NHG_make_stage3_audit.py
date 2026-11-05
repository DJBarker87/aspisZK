"""Extend the retained import/audit manifest; never rerun a passing old batch."""
from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent
revision='6ff7634f515'
def old(n):return subprocess.check_output(['git','show',revision+':'+str(E.relative_to(Path.cwd())/n)])
modules=['NHG_FieldBounds','NHG_FrontierFrame','NHG_FrontierPackets','NHG_PublicCarrier','NHG_StdBytes','NHG_ProducerDomains','NHG_ProducerWidths','NHG_ProducerPackets','NHG_ProgramChain','NHG_AppendFrame','NHG_SnapshotViews','NHG_BeginFrame','NHG_Product','NHG_FrontComposition']
roots=['AspisR1.'+m+'.'+n for m in modules for n in re.findall(r'^theorem (\w+)',(E/(m+'.lean')).read_text(),re.M)]
prior=json.loads(old('NHG_AUDIT_ROOTS.json'));assert len(prior['groups'])==3
prior['groups'] += [roots[i:i+12]for i in range(0,len(roots),12)]
(E/'NHG_AUDIT_ROOTS.json').write_text(json.dumps(prior,indent=1)+'\n')
base=old('NHG_COMBINED_IMPORT.lean').decode();imports=''.join(l+'\n'for l in base.splitlines()if l.startswith('import '))
allroots=[r for g in prior['groups']for r in g]
(E/'NHG_COMBINED_IMPORT.lean').write_text(imports+''.join('import '+m+'\n'for m in modules)+''.join('#print axioms '+r+'\n'for r in allroots))
rows=list(map(json.loads,old('NHG_EXPECTED_IMPORTS.jsonl').splitlines()));rows=[r for r in rows if r['module']!='NHG_COMBINED_IMPORT']
for m in modules+['NHG_COMBINED_IMPORT']:
 assert not any(r['module']==m for r in rows)
 rows.append(dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)))
(E/'NHG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in rows))
seal={}
for n in ['NHG_validate.py','NHG_STAGE2_VALIDATION.json','NHG_MUTATION_RESULTS.json','NHG_CLOSED.json','NHG_LEDGER_DELTA.json','NHG_COMBINED_IMPORT.lean','NHG_AUDIT_ROOTS.json','NHG_EXPECTED_IMPORTS.jsonl']:
 data=old(n);seal[n]=dict(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
(E/'NHG_STAGE2_SEAL.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse',revision],text=True).strip(),files=seal,rule='Old checks remain byte-identical and their PASS inputs/results remain in this immutable git revision. Stage3 adds checks; it does not replace any old certificate or raw root.'),indent=1)+'\n')
(E/'NHG_STAGE3_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,batches=list(range(3,len(prior['groups']))),retained_batches=[0,1,2],joint_target='NHG_COMBINED_IMPORT',headline='AspisR1.RPx_Deployed.deployed'),indent=1)+'\n')
print(len(roots),'new roots;',len(allroots),'total;',len(rows),'expected modules')
