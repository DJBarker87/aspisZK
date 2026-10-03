#!/usr/bin/env python3
import pathlib,hashlib,json,subprocess,shlex
root=pathlib.Path(__file__).resolve().parents[2];local=pathlib.Path(__file__).resolve().parent
src=local/'R519SharedGammaPartsLiteralReadsV3.llbc';sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha=='984c87c8a20e301e2c10482b8a723d228684236baa29d51fd426bf85c8531cdd'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r519-parts-v3-20261003-a'
binary='/home/dombarker/project-offloads/aspis-r490-slice-len-concrete-20261003-a/aeneas-r497-slice-len-concrete-candidate';binary_sha='85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b'
subprocess.run(['ssh',*opts,host,'mkdir -p '+shlex.quote(remote+'/generated')],check=True)
subprocess.run(['scp',*opts,str(src),host+':'+remote+'/R519SharedGammaPartsLiteralReadsV3.llbc'],check=True)
argv=[binary,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR519SharedGammaPartsV3','-dest',remote+'/generated','-subdir','AspisR519SharedGammaPartsV3','-split-files','-emit-json',remote+'/R519SharedGammaPartsLiteralReadsV3.llbc']
script=f'''import pathlib,subprocess,hashlib,json,re
root=pathlib.Path({remote!r})
assert hashlib.sha256(pathlib.Path({binary!r}).read_bytes()).hexdigest()=={binary_sha!r}
assert hashlib.sha256((root/'R519SharedGammaPartsLiteralReadsV3.llbc').read_bytes()).hexdigest()=={sha!r}
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 name=line.split()[0]
 if not name.startswith('aspis'):continue
 prop=subprocess.check_output(['systemctl','--user','show',name,'-p','MemoryMax'],text=True).strip().split('=',1)[1]
 assert prop.isdigit(),(name,prop);reservations.append((name,int(prop)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
(root/'launch.json').write_text(json.dumps({{'target':'R519 V3 omits two unused global export groups after five exact Const rewrites; global rows retained','argv':{argv!r},'source_revision':{revision!r},'llbc_sha256':{sha!r},'binary_sha256':{binary_sha!r},'reservations_before_launch':reservations,'caps':{{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}}}},indent=2)+'\\n')
with (root/'aeneas.log').open('w') as out: result=subprocess.run(['/usr/bin/time','-v',*{argv!r}],stdout=out,stderr=subprocess.STDOUT)
txt=(root/'aeneas.log').read_text()
def metric(p):
 m=re.search(p,txt);return m.group(1) if m else None
(root/'receipt.json').write_text(json.dumps({{'target':'R519 V3 selected parts closure after omission of unused global export groups','source_revision':{revision!r},'llbc_sha256':{sha!r},'binary_sha256':{binary_sha!r},'exit_status':result.returncode,'wall_time':metric(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (\\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \\(kbytes\\): (\\d+)'),'swaps':metric(r'Swaps: (\\d+)'),'formal_axioms':'N/A translation only; generated Lean not yet compiled'}},indent=2)+'\\n')
print(json.dumps({{'exit_status':result.returncode,'wall_time':metric(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (\\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \\(kbytes\\): (\\d+)'),'swaps':metric(r'Swaps: (\\d+)'),'log_path':str(root/'aeneas.log')}},indent=2));raise SystemExit(result.returncode)
'''
(local/'v3-translate-command.json').write_text(json.dumps({'argv':argv,'llbc_sha256':sha,'source_revision':revision,'binary_sha256':binary_sha,'remote_workspace':remote,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}},indent=2)+'\n')
command=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r519-parts-v3','--working-directory='+remote,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',script]
with (local/'v3-translation-ssh.log').open('w') as out:result=subprocess.run(['ssh',*opts,host,shlex.join(command)],stdout=out,stderr=subprocess.STDOUT)
print((local/'v3-translation-ssh.log').read_text())
subprocess.run(['scp','-r',*opts,host+':'+remote,str(local/'saved-output-v3')],check=True)
raise SystemExit(result.returncode)
