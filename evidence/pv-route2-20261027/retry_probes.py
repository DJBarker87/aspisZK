from pathlib import Path
import json,sys,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027');exec((D/'run_host.py').read_text().split('roots=')[0])
for op in map(int,sys.argv[1:]):
 first=D/f'charon-{op}-01'/'target.json';cmd=json.loads(first.read_text())['target'];cmd[cmd.index('--mir')+1]='optimized';llbc=D/f'PV_R2_{op}_Opt.llbc';cmd[cmd.index('--dest-file')+1]=str(llbc)
 if run(f'charon-{op}-02-opt',cmd,D/'probes'/str(op)):continue
 out=D/f'generated-{op}-opt';out.mkdir();run(f'aeneas-{op}-02-opt',['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_{op}_Opt','-dest',str(out),'-split-files','-emit-json',str(llbc)])
