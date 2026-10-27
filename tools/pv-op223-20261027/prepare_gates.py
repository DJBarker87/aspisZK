from pathlib import Path
import subprocess,json
P=Path('tools/pv-op223-20261027');D='/home/dombarker/project-offloads/codex-pv-op223-20261027';OLD='/home/dombarker/project-offloads/codex-pv-rebase-20261026';H='dombarker@100.108.41.90'
# Native control reuse is justified by exact implementation equality; no second control workspace.
assert not subprocess.check_output(['git','diff','258c685f50','3f9177b647','--','crates','programs','Cargo.lock'])
for name in ['build.py','native.py']:
 s=subprocess.check_output(['git','show','codex/pv-rebase-20261026:tools/pv-rebase-20261026/'+name],text=True).replace(OLD,D)
 s=s.replace("W/'src'","W/'source'")
 # Reuse pinned compiled caches rather than copy them or make another source workspace.
 s=s.replace("H/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')","Path('"+OLD+"')/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')").replace("H/'native-target'","Path('"+OLD+"/native-target')")
 s=s.replace("str(W/'source-revision.txt')","str(H/'source-revision.txt')")
 # Resolve candidate at the assigned host root, no extra checkout.
 s=s.replace("W=H/who","W=H")
 # Admission output must be preserved before launches.
 s=s.replace("pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')]);assert pre.returncode==0,pre.returncode","pre=subprocess.run(['python3',str(H/'reservation.py'),str(out/'reservation.json')],stdout=open(out/'reservation.log','w'),stderr=subprocess.STDOUT);\nif pre.returncode:sys.exit(pre.returncode)")
 (P/name).write_text(s)
 # Exact existing wrapper/diagnostic APIs remain unchanged.
 subprocess.run(['scp','-q',str(P/name),H+':'+D+'/'+name],check=True)
subprocess.run(['ssh',H,'cp '+OLD+'/reservation.py '+D+'/reservation.py; cp '+OLD+'/rustc-diagnostics.py '+D+'/rustc-diagnostics.py; cp '+OLD+'/capped-template.py '+D+'/capped-template.py; ln -s '+OLD+'/candidate '+D+'/baseline'],check=True)
# Prepared timing uses baseline control, candidate output root via a symlink.
s=(P/'timing.py').read_text().replace("'research'","'baseline'")
(P/'timing.py').write_text(s)
subprocess.run(['ssh',H,'mkdir -p '+D+'/candidate; ln -s ../bin '+D+'/candidate/bin; ln -s ../build-fixture '+D+'/candidate/build-fixture; ln -s ../source-revision.txt '+D+'/candidate/source-revision.txt; cp '+OLD+'/quiet-preflight.py '+D+'/quiet-preflight.py'],check=True)
subprocess.run(['scp','-q',str(P/'timing.py'),H+':'+D+'/timing.py'],check=True)
