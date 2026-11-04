"""Reuse NEP's fixed raw walker and private importAll driver, changing roots only."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path('evidence/pv-stx-20261104');P='evidence/axaudit2-20261102/'
walker=subprocess.check_output(['git','show','research:'+P+'NEP_WALKER.lean'],text=True)
driver=subprocess.check_output(['git','show','research:'+P+'NEP_Driver.lean'],text=True)
(E/'audit-tool').mkdir(exist_ok=True)
(E/'audit-tool/NEP_WALKER.lean.txt').write_text(walker)
(E/'audit-tool/NEP_Driver.lean.txt').write_text(driver)
# Preserve the walker literally, including HARD ERROR on an unresolved name.
Path('lean/PV_STX_AuditWalker.lean').write_text(walker)
roots=[];modules=[]
for p in sorted(Path('lean').glob('PV_STX_*.lean')):
 if p.stem.startswith('PV_STX_Audit'):continue
 ns=re.search(r'^namespace (\S+)',p.read_text(),re.M)[1]
 found=re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)
 if found:modules.append(p.stem);roots += [n if n.startswith(ns+'.') else ns+'.'+n for n in found]
start=driver.index('  let (modules, roots) :=')
end=driver.index('  let env ←',start)
new=driver[:start]+'  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'+driver[end:]
new=new.replace('import NEP_WALKER','import PV_STX_AuditWalker')
Path('lean/PV_STX_AuditDriver.lean').write_text(new)
(E/'audit-tool/manifest.json').write_text(json.dumps(dict(authority='research:'+P+'NEP_Driver.lean and NEP_WALKER.lean (ax1\u2032)',research_revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip(),walker_sha256=hashlib.sha256(walker.encode()).hexdigest(),walker_byte_identical=True,driver_original_sha256=hashlib.sha256(driver.encode()).hexdigest(),driver_sha256=hashlib.sha256(new.encode()).hexdigest(),driver_changes=['import module filename only','module and theorem root arrays only'],modules=modules,roots=roots,qualifier='Private importAll loader; hard error on every unresolved constant; cached summaries used only for post-walk comparison.'),indent=2)+'\n')
print(len(roots),'audit roots')
