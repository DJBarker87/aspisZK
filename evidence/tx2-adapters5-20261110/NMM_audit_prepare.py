from pathlib import Path
import subprocess,json,re,hashlib,difflib
E=Path(__file__).resolve().parent
read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],text=True)
mods=['NMM_LaneTranscription','NMM_LaneReplies','NMM_RegistryTranscription','NMM_Ownership233','NMM_AccountsTranscription','NMM_PdaProjection','NMM_OutcomeCases','NMM_LaneScalarLoop','NMM_LaneScalarSource','NMM_LaneAcceptance','NMM_PayloadComponents','NMM_LaneSymbolic','NMM_LaneSuccess']
receipts=[json.loads(l) for l in (E/'NMM_ATTEMPTS.jsonl').read_text().splitlines()]
roots=[]
for m in mods:
 p=E/(m+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert any(x.get('kind')=='lean' and x.get('module')==m and x.get('exit_status')==0 and h in x['source_hashes'].values() for x in receipts),m
 s=p.read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 roots.extend(ns+'.'+n for n in re.findall(r'^\s*theorem (\w+)',s,re.M))
roots=list(dict.fromkeys(roots));allroots=roots+['AspisR1.RPx_Deployed.deployed']
(E/'NMM_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[allroots],roots=allroots,new_roots=roots,scope='Only new support roots plus headline; no candidate root yet'),indent=1)+'\n')
s='import NLX_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'
s+='\n'.join('#print '+r+'\n#print axioms '+r for r in allroots)+'\n'
(E/'NMM_COMBINED_IMPORT.lean').write_text(s)
expected={}
for path in ['evidence/ledger24-20261110/NLX_EXPECTED_IMPORTS.jsonl','evidence/tx2-adapters4-20261110/NLK_EXPECTED_IMPORTS.jsonl']:
 for l in read(path).splitlines():
  x=json.loads(l);n=x['module'];v=x['imports'];assert n not in expected or expected[n]==v,n;expected[n]=v
for m in mods+['NMM_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NMM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=read('evidence/tx2-adapters4-20261110/NLK_ScanDriver.lean')
new=old.replace('NLK_COMBINED_IMPORT','NMM_COMBINED_IMPORT').replace('NLK_EXPECTED_IMPORTS','NMM_EXPECTED_IMPORTS').replace('NLK_LOADED_scan','NMM_LOADED_scan')
(E/'NMM_ScanDriver.lean').write_text(new)
(E/'NMM_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NLK_ScanDriver.lean',tofile='NMM_ScanDriver.lean')))
(E/'NMM_audit_one.py').write_text(read('evidence/tx2-adapters4-20261110/NLK_audit_one.py').replace('NLK_binary_','NMM_binary_'))
(E/'NMM_SEMANTIC_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(allroots),expected_imports=len(expected))))
