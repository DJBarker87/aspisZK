from pathlib import Path
from run import H,run
import json,subprocess,sys,hashlib
R=H/'resume17'
if '--inside' not in sys.argv:
 label='N73926';retry=0
 while (R/label).exists():
  assert not (R/label/'receipt/receipt.json').exists();retry+=1;label='N73926-r'+str(retry)
 raise SystemExit(run('resume17/'+label,['python3',str(Path(__file__)),'--inside'],'missing configuration artifact: restore getrandom/std to deployed graph, reproduce all accepted terminal/copy emissions byte-identically',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false'}))
rows=[]
for group in ['terminal','copy']:
 s=subprocess.run(['python3',str(H/'direct_group227_resume17_host.py'),group+'-features','73926','--inside']).returncode;assert s==0
 old=R/('direct-'+group);new=R/('direct-'+group+'-features')
 for row in json.loads((new/'results.json').read_text()):
  assert row['status']=='EXTRACTED',row
  name=row['function'].replace('::','__')
  for f in ['Types.lean','Funs.lean']:
   a=(old/name/'generated'/f).read_bytes();b=(new/name/'generated'/f).read_bytes();assert a==b,(name,f)
   rows.append(dict(function=row['function'],file=f,sha256=hashlib.sha256(b).hexdigest(),byte_identical=True))
(R/'feature-reproduction.json').write_text(json.dumps(dict(reason='Original driver lost getrandom/std, an unreached dependency feature. Restored deployed dependency-feature graph; all accepted emissions regenerated unchanged.',comparisons=rows),indent=2)+'\n')
