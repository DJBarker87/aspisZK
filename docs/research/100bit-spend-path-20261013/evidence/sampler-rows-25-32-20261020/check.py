#!/usr/bin/env python3
"""One focused local Lean check, serialized and receipted; no dependency builds."""
import sys,os,json,hashlib,subprocess,time
from pathlib import Path
base=Path(__file__).resolve().parents[2]
ev=Path(__file__).resolve().parent
module=sys.argv[1]; attempt=sys.argv[2]
source=base/'lean'/f'{module}.lean'
out=ev/attempt;out.mkdir()
objects=Path('/tmp/codex-cx-sampler-20261020-objects');objects.mkdir(exist_ok=True)
cache=Path('/tmp/r1-circle-pointwise-coalesced-local-v1/objects')
paths=[str(objects),str(cache),'/tmp/lean432-nuc-aeneas-cache','/tmp/root-terminal-named-types-20261019/objects','/tmp/literal-acceptance-terminal-object-reuse/objects','/tmp/root-finish-prefix-deps-20261018']
paths += [p for p in json.loads(Path('/tmp/r1-circle-pointwise-coalesced-local-v1/manifest.json').read_text())['ordered_roots'] if Path(p).exists()]
paths += ['/tmp/gs-bytebank-project-closure-local/objects','/tmp/gs-secondfold-project-closure-20261019-v2/objects','/tmp/gs-byte-extractor-compiled-objects-20261019/objects','/tmp/query-checked-extractor-direct-owners-20261019','/tmp/lean432-gather-array-objects','/tmp/checks-schedule-deps-20261019/objects','/tmp/gs-byte-extractor-deps-20261019/objects','/tmp/aspis-root-local-semantic-20261015/objects']
paths += [str(p) for p in Path('/Users/dominic/ZK/AspisFormal/.lake/packages').glob('*/.lake/build/lib/lean')]
rr=json.loads((base/'evidence/rr-total-normalization-query-cost-20261019/RRConcreteRawStateValidity/command.json').read_text())
paths += [p for p in rr['environment']['LEAN_PATH'].split(':') if Path(p).exists()]
paths += sorted(str(p) for p in Path('/tmp/root-checked-components-native-evidence-20261019').glob('*/objects') if p.is_dir())
fmt=json.loads((base/'evidence/checks-derived-adaptive-injection-20261019/RawChecksInjectionFormat/command.json').read_text())
paths += [p for p in fmt['lean_path'].split(':') if Path(p).exists()]
packages=[str(p) for p in Path('/Users/dominic/ZK/AspisFormal/.lake/packages').glob('*/.lake/build/lib/lean')]
paths=[str(objects)]+packages+paths[1:]
if module == 'RawDeployedTranscriptFormat':
 paths=[str(objects)]+[p for p in fmt['lean_path'].split(':') if Path(p).exists()]+paths[1:]
env=dict(os.environ,LEAN_PATH=':'.join(dict.fromkeys(paths)))
lean='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
argv=[lean,'-j1','-M4400','-DElab.async=false','-R',str(base/'lean'),'-o',str(objects/f'{module}.olean'),str(source)]
command={'argv':argv,'env':{'LEAN_PATH':env['LEAN_PATH']},'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
(out/'command.json').write_text(json.dumps(command,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode==0:time.sleep(60)
 start=time.monotonic()
 with (out/'lean.log').open('w') as log:
  r=subprocess.run(['/usr/bin/time','-l','-o',str(out/'time.log')]+argv,env=env,stdout=log,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-start
finally:lock.rmdir()
log=(out/'lean.log').read_text();tim=(out/'time.log').read_text()
receipt={'schema':'focused-extractor-proof-packet-v1','module':module,'attempt':attempt,**command,'exit_status':r.returncode,'wall_seconds':elapsed,'time_log':tim,'axioms_lines':[s for s in log.splitlines() if 'depends on axioms' in s or s.startswith(' [')],'errors':log if r.returncode else None}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(log);print(tim);print('EXIT',r.returncode)
sys.exit(r.returncode)
