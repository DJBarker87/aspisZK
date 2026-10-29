"""Verify receipt input hashes against frozen git objects and resource policy."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-cx-20261029';rev='27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1'
checks=[]
for p in sorted(E.glob('N*/receipt.json')):
 d=json.loads(p.read_text());c=json.loads(p.with_name('command.json').read_text());ad=json.loads(p.with_name('reservation.log').read_text());assert ad['allowed'] is True
 assert d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],[str(6*2**30),str(8*2**30),'0','64']))
 assert d['source_revision']==rev and d['swaps']==0
 pairs=list(c['input_sha256'].items());proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for f,h in pairs:
  proc.stdin.write((rev+':'+f+'\n').encode());proc.stdin.flush();line=proc.stdout.readline().decode().split();assert len(line)==3,(f,line);n=int(line[2]);b=proc.stdout.read(n);assert proc.stdout.read(1)==b'\n';assert hashlib.sha256(b).hexdigest()==h,f
 proc.stdin.close();assert proc.wait()==0
 checks.append(dict(attempt=p.parent.name,input_files=len(pairs),all_byte_equal_frozen_git=True,exit_status=d['exit_status'],wall_seconds=d['wall_seconds'],peak_rss_kib=d['peak_rss_kib'],swaps=d['swaps'],cgroup_peak_bytes=d['cgroup_peak_bytes']))
changed=subprocess.check_output(['git','diff',rev,'--name-only'],cwd=R,text=True).splitlines();assert not any(p.startswith(('crates/','programs/','tools/r1-cost-probe/')) for p in changed)
(E/'checks.json').write_text(json.dumps(dict(source_revision=rev,receipts=checks,frozen_paths_unchanged=True,lean_attempts=0,kani_runs=0),indent=2)+'\n')
print(json.dumps(checks,indent=2))
