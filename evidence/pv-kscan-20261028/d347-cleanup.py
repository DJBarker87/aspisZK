from pathlib import Path
import hashlib,json,shutil,subprocess
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028');D=R/'d347';assert D.resolve()==D
ps=subprocess.check_output(['ps','-eo','args'],text=True).splitlines();live=[p for p in ps if str(R/'d347-run.py') in p and not p.startswith(('bash -c','sh -c'))];assert not live,live
pins={}
for name in ['cbmc','goto-instrument','kani-compiler','kani-driver']:
 p=Path('/home/dombarker/.kani/kani-0.67.0/bin')/name;pins[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
pins['cbmc_version']=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--version'],text=True).strip();(D/'tool-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
removed=[]
for p in [D/'cache',*sorted(D.glob('D*/target'))]:
 if not p.exists():continue
 assert p.is_relative_to(D) and not p.is_symlink();size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file() and not f.is_symlink());removed.append(dict(path=str(p),bytes=size,kind='own rebuildable codegen cache'));shutil.rmtree(p)
for d in D.glob('D*/package'):
 for p in d.rglob('*'):
  if p.is_file() and (p.name.endswith(('.out','.rlib','.rmeta','.o'))):
   removed.append(dict(path=str(p),bytes=p.stat().st_size,kind='own standalone goto/object artifact; hashes and metadata retained'));p.unlink()
report=dict(removed=removed,removed_bytes=sum(x['bytes'] for x in removed),retained='Own source packages, exact per-run input overlays, source checks, receipts and raw graph inventories; all historical reused artifacts in other directories untouched.',active_own_codegen_scopes=live,keys='No wallet/account keys created, read, changed or deleted',print_axioms='N/A: no Lean')
(D/'cleanup.json').write_text(json.dumps(report,indent=2)+'\n');print(report['removed_bytes'],'bytes removed')
