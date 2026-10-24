#!/usr/bin/env python3
"""Inspect immutable historical receipts; no working tree or gate consumption."""
import json,hashlib,subprocess,time,resource
from pathlib import Path
BASE='3e9998bbfc828c6e9455cc45a846dcd0f5372710';E=Path('evidence/sbf-identity-20261024');P='docs/research/100bit-spend-path-20261013/';t=time.monotonic();inputs={}
def read(p):
 b=subprocess.check_output(['git','show',BASE+':'+p]);inputs[p]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),git_blob=subprocess.check_output(['git','rev-parse',BASE+':'+p],text=True).strip());return b
s10=P+'evidence/s10-repin3-20261023/'
s=json.loads(read(s10+'source-inputs.json')); modes={}
for mode in ['default','devnet','pool']:
 modes[mode]={k:json.loads(read(s10+'build-'+mode+'-v1/'+k+'.json')) for k in ['command','receipt','artifact-comparison','reservation']}
for name in ['build-manifest.json','receipt-target-corrections.json','comparison-provenance.json','snapshot-exclusions.json']:read(s10+name)
old=json.loads(read(P+'evidence/s2-trust-20261023/production-pins.json'));archives=json.loads(read(P+'evidence/s2-trust-20261023/sbf-archive-pins.json'))
parser=read(P+'evidence/parser-candidate-v152-sbf-20261014/toolchain-pins.txt').decode()
for p in ['tools/s10-repin3-20261023/build-host.py','tools/s10-repin3-20261023/rustc-diagnostics.py','tools/s10-repin3-20261023/prepare-host.py','tools/s10-repin3-20261023/snapshot.py','evidence/port24sbfmap-20261024/REPORT.md','evidence/port24sbfmap-20261024/manifest.json',P+'lean/R1FinalSoundness.lean',P+'design/R1-PREMISES-REACCEPTANCE-20261020.md']:
 read(p)
current=json.load(open(E/'current-content.json'))['pins'];matched=[]
for a in archives['archives']:
 matched.append(dict(path=a['path'],historical_receipt_sha256=a['sha256'],current_sha256=current[a['path']]['sha256'],match=a['sha256']==current[a['path']]['sha256']))
rustc='/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc'
matched.append(dict(path=rustc,historical_receipt_sha256=old['sbf']['rustc_sha256'],current_sha256=current[rustc]['sha256'],match=old['sbf']['rustc_sha256']==current[rustc]['sha256']))
# A direct exact-string search of relevant historical metadata, retained as discovery,
# not proof that no other custodian possesses a contemporaneous receipt.
searchcmd=['git','grep','-I','-n','-E','d95c95b68e321ad7|a1f52278d174e074|6a7f83ac4e22637d|790f1537507dbdb0',BASE,'--',s10+'*.json',P+'evidence/s10-inventory*/**/toolchains.txt',P+'evidence/s10-current-repin-20261020/*.json']
x=subprocess.run(searchcmd,capture_output=True,text=True)
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r=dict(schema='sbf-immutable-assessment-v1',base=BASE,source_revision=s['source_revision'],source_input_manifest=inputs[s10+'source-inputs.json'],source_input_count=len(s['files']),modes=modes,older_receipt_matches=matched,older_receipt_source=old['source_revision'],older_receipt_limitations=old['limitations'],old_parser_toolchain_metadata=parser,assessment='Older rustc/core/std hashes match CURRENT installation. No alloc/compiler-driver/full-source contemporaneous pre/go/post identity receipt recovered; older sources/artifact pins differ. No retroactive S10 identity gate.',inputs=inputs,historical_search=dict(command=searchcmd,exit=x.returncode,stdout=x.stdout,stderr=x.stderr),receipt=dict(command=['python3','tools/sbf-identity-20261024/inspect-immutable.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,print_axioms='N/A: read-only metadata'))
(E/'immutable-assessment.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(modes={k:{x:v['receipt'][x] for x in ['wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']} for k,v in modes.items()},older_matches=matched,inputs=len(inputs),source_count=len(s['files'])),indent=2))
