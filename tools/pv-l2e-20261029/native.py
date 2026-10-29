"""One optimized, capped sampler finite check with a matched failing control."""
from pathlib import Path
import json,subprocess,shlex,time,hashlib,re
E=Path('evidence/pv-l2e-20261029');H='/home/dombarker/project-offloads/codex-pv-l2e-20261029';host='dombarker@100.108.41.90'
for f in E.glob('refusal-*.json'):assert time.time()-json.load(open(f))['epoch']>=180
assert not (E/'receipt-sampler-native.json').exists()
def ssh(cmd):return subprocess.run(['ssh',host,cmd],text=True,capture_output=True)
for a,b in [('tools/pv-l2e-20261029/sampler-native.rs','sampler-native.rs'),('evidence/pv-l2e-20261029/sampler-raw.rs.txt','raw.rs')]:
 assert subprocess.check_output(['git','show','HEAD:'+a])==Path(a).read_bytes()
 r=subprocess.run(['scp','-q',a,host+':'+H+'/'+b]);assert r.returncode==0
script=f'''set -eu
/home/dombarker/.cargo/bin/rustup run 1.94.1 rustc --version --verbose > {H}/evidence/sampler-rustc.log
/home/dombarker/.cargo/bin/rustup run 1.94.1 rustc -O --edition=2021 -C overflow-checks=off -C debug-assertions=off -C codegen-units=1 -C link-arg=-Wl,--threads=4 {H}/sampler-native.rs -o {H}/sampler-native
{H}/sampler-native
set +e
{H}/sampler-native negative > {H}/evidence/sampler-negative.log 2>&1
status=$?
set -e
printf 'negative_exit=%s\\n' "$status"
test "$status" = 101
sha256sum {H}/sampler-native
'''
r=ssh('cat > '+shlex.quote(H+'/sampler-native.sh')+' <<\'PVSCRIPT\'\n'+script+'\nPVSCRIPT');assert r.returncode==0
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-l2e-sampler-native','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+'/evidence/time-sampler-native.log','sh',H+'/sampler-native.sh']
admit=f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/admission-sampler-native.json > {H}/evidence/admission-sampler-native.log 2>&1'
check='python3 -c '+shlex.quote('import json;assert json.load(open('+repr(H+'/evidence/admission-sampler-native.json')+'))["allowed"] is True')
intent=dict(target='four exact source sampler helper bodies vs list-style arithmetic reference',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,expected_time='optimized standalone rustc compilation, followed by 76304 finite full-state checks; no large elimination',evidence_class='finite native validation',profile='rustc 1.94.1 -O, debug assertions off, overflow checks off',features='standalone bodies: no cfg alternatives or dependencies; no full deployed-crate or ELF credit',axioms='N/A: native validation',source_sha256=hashlib.sha256(Path('tools/pv-l2e-20261029/sampler-native.rs').read_bytes()).hexdigest(),raw_source_sha256=hashlib.sha256(Path('evidence/pv-l2e-20261029/sampler-raw.rs.txt').read_bytes()).hexdigest())
(E/'submission-sampler-native.json').write_text(json.dumps(intent,indent=2)+'\n')
r=ssh(admit+' && '+check+' && '+shlex.join(cmd)+f' > {H}/evidence/out-sampler-native.log 2>&1');intent['transport_exit']=r.returncode
for name in ['admission-sampler-native.json','admission-sampler-native.log','out-sampler-native.log','time-sampler-native.log','sampler-rustc.log','sampler-negative.log']:
 q=ssh('cat '+H+'/evidence/'+name);(E/name).write_text(q.stdout+q.stderr)
a=json.load(open(E/'admission-sampler-native.json'))
if not a['allowed']:
 (E/'refusal-sampler-native.json').write_text(json.dumps(dict(epoch=time.time(),admission=a,compiler_started=False)));(E/'submission-sampler-native.json').unlink();raise SystemExit(78)
out=(E/'out-sampler-native.log').read_text();tim=(E/'time-sampler-native.log').read_text()
for key,pat in dict(exit=r'Exit status: (\d+)',rss_kib=r'Maximum resident set size \(kbytes\): (\d+)',swaps=r'Swaps: (\d+)',wall=r'Elapsed.*: (\S+)').items():intent[key]=re.search(pat,tim)[1]
intent['admission']=a;intent['output']=out
(E/'receipt-sampler-native.json').write_text(json.dumps(intent,indent=2)+'\n');print(out);print(intent['exit']);raise SystemExit(int(intent['exit']))
