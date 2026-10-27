from pathlib import Path
import ast,hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;errors=[]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p in E.glob('*.py'):ast.parse(p.read_text())
for p in E.rglob('*.json'):json.loads(p.read_text())
for p in sorted(E.glob('XRi_K*/receipt.json')):
 x=json.loads(p.read_text())
 for n,s in x['source_hashes'].items():
  if digest(E/n)!=s:errors.append('Kani source mismatch '+n)
 if x['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('limits '+str(p))
 if x['swaps']!='0':errors.append('swap '+str(p))
x=json.loads((E/'XRi_L002/receipt.json').read_text())
if digest(E/'XRi_Types.lean.txt')!=next(iter(x['source_hashes'].values())):errors.append('raw Lean source hash')
if x['exit_status']!=1 or x['print_axioms']:errors.append('unexpected Lean outcome')
pins=json.loads((R/'evidence/extraction-eval1-20261027/XRh_pinned_outputs_01.json').read_text())['outputs']
for row in pins:
 n=Path(row['path']).name
 if n.endswith('.lean') and digest(E/('XRi_'+n+'.txt'))!=row['sha256']:errors.append('generated raw hash '+n)
for n in ['ARX_Root','Rc10_Top']:
 if len({digest(E/('XRi_'+n+'.'+s+'.lean.txt')) for s in ['BEFORE','AFTER']}|{digest(R/'lean'/(n+'.lean'))})!=1:errors.append('top changed '+n)
for row in json.loads((E/'XRi_recount.json').read_text())['baseline']:
 if digest(R/row['path'])!=row['sha256']:errors.append('baseline changed '+row['path'])
for row in json.loads((E/'XRi_HostAudit.json').read_text())['pins']:
 n=Path(row['path']).name
 if n.startswith('S2W_') and digest(E/('XRi_'+n))!=row['sha256']:errors.append('runner changed '+n)
q=subprocess.run(['git','diff','--check','b18724f56f^..HEAD','--','*.md','*.py','*.json','*.rs','*.toml','*.lean'],cwd=R,text=True,capture_output=True)
if q.returncode:errors.append('source/metadata whitespace: '+q.stdout)
paths=subprocess.check_output(['git','diff','--name-only','b18724f56f^..HEAD'],cwd=R,text=True).splitlines()
if any(not p.startswith('evidence/extraction-assoc1-20261027/') for p in paths):errors.append('outside job directory')
if any(p.suffix in ['.olean','.ir','.o','.so','.elf','.tar','.gz'] for p in E.rglob('*') if p.is_file()):errors.append('binary artifact')
result=dict(errors=errors,budget=dict(lean_compiles=1,lean_limit=100,additional_preflights=1,kani_runs=10,kani_limit=10,extraction_invocations=0),generated_bytes_unchanged=True,top_and_ledger_contract_unchanged=True,raw_generator_and_stdout_whitespace='Preserved as original evidence; not normalized',source_metadata_whitespace_exit=q.returncode)
(E/'XRi_Verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert not errors
