#!/usr/bin/env python3
import pathlib,hashlib,json,subprocess,shlex
root=pathlib.Path(__file__).resolve().parents[2];local=pathlib.Path(__file__).resolve().parent
src=local/'R519SharedGammaPartsLiteralReads.llbc';sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha=='ed7ec2337267ab761c11aca1ad0a177c4ee9fa7528cc9087298b89a80c857100'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r519-literal-global-parts-20261003-a'
binary='/home/dombarker/project-offloads/aspis-r490-slice-len-concrete-20261003-a/aeneas-r497-slice-len-concrete-candidate';binary_sha='85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b'
subprocess.run(['ssh',*opts,host,'mkdir -p '+shlex.quote(remote+'/generated')],check=True)
subprocess.run(['scp',*opts,str(src),host+':'+remote+'/R519SharedGammaPartsLiteralReads.llbc'],check=True)
argv=[binary,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR519SharedGammaPartsLiteralReads','-dest',remote+'/generated','-subdir','AspisR519SharedGammaPartsLiteralReads','-split-files','-emit-json',remote+'/R519SharedGammaPartsLiteralReads.llbc']
script=f'''import pathlib,subprocess,hashlib,json,re
root=pathlib.Path({remote!r})
assert hashlib.sha256(pathlib.Path({binary!r}).read_bytes()).hexdigest()=={binary_sha!r}
assert hashlib.sha256((root/'R519SharedGammaPartsLiteralReads.llbc').read_bytes()).hexdigest()=={sha!r}
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 name=line.split()[0]
 if not name.startswith('aspis'):continue
 prop=subprocess.check_output(['systemctl','--user','show',name,'-p','MemoryMax'],text=True).strip().split('=',1)[1]
 assert prop.isdigit(),(name,prop);reservations.append((name,int(prop)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
(root/'launch.json').write_text(json.dumps({{'target':'R519 exact captured literal operands for P and u32::MAX; five operand nodes only','argv':{argv!r},'source_revision':{revision!r},'llbc_sha256':{sha!r},'binary_sha256':{binary_sha!r},'reservations_before_launch':reservations,'caps':{{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}}}},indent=2)+'\\n')
with (root/'aeneas.log').open('w') as out: result=subprocess.run(['/usr/bin/time','-v',*{argv!r}],stdout=out,stderr=subprocess.STDOUT)
txt=(root/'aeneas.log').read_text()
def metric(p):
 m=re.search(p,txt);return m.group(1) if m else None
(root/'receipt.json').write_text(json.dumps({{'target':'R519 literal operand normalization: exact selected parts closure','source_revision':{revision!r},'llbc_sha256':{sha!r},'binary_sha256':{binary_sha!r},'exit_status':result.returncode,'wall_time':metric(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (\\S+)'),'peak_rss_kib':metric(r'Maximum resident set size \\(kbytes\\): (\\d+)'),'swaps':metric(r'Swaps: (\\d+)'),'formal_axioms':'N/A translation only; generated Lean not yet compiled'}},indent=2)+'\\n')
print(txt);raise SystemExit(result.returncode)
'''
(local/'literal-read-translate-command.json').write_text(json.dumps({'argv':argv,'llbc_sha256':sha,'source_revision':revision,'binary_sha256':binary_sha,'remote_workspace':remote,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}},indent=2)+'\n')
command=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r519-literal-global-parts','--working-directory='+remote,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',script]
with (local/'literal-read-translation-ssh.log').open('w') as out:result=subprocess.run(['ssh',*opts,host,shlex.join(command)],stdout=out,stderr=subprocess.STDOUT)
print((local/'literal-read-translation-ssh.log').read_text())
subprocess.run(['scp','-r',*opts,host+':'+remote,str(local/'saved-output-literal-reads')],check=True)
raise SystemExit(result.returncode)
