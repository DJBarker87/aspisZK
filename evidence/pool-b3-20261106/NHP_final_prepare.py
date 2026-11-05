from pathlib import Path
import json,subprocess,sys,hashlib,shutil
E=Path(__file__).resolve().parent
p=E/'NHP_COMBINED_IMPORT.lean';s=p.read_text()
for module in ['NHP_ErrorModel','NHP_SeedGeometry']:
 if 'import '+module+'\n' not in s:s='import '+module+'\n'+s
s+='\n#print axioms NHP_ErrorModel.result_domain\n#print axioms NHP_SeedGeometry.no_wrap\n';p.write_text(s)
subprocess.run([sys.executable,str(E/'NHP_audit_prepare.py')],check=True)
p=E/'NHP_AUDIT_ROOTS.json';x=json.loads(p.read_text());x['roots']=sorted(set(x['roots']+['NHP_ErrorRef.NHP_error_reference.classify']));x['groups']=[x['roots'],x['roots']];p.write_text(json.dumps(x,indent=1)+'\n')
p=E/'NHP_LOADED_scan.jsonl';q=E/'NHP_BASE_LOADED_scan.jsonl'
if not q.exists():shutil.copy2(p,q)
print(json.dumps(dict(final_roots=len(x['roots']),baseline_scan_sha256=hashlib.sha256(q.read_bytes()).hexdigest())))
