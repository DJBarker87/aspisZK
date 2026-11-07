"""Own sequential native validation inside ONE existing capped S2W scope."""
from pathlib import Path
import json,subprocess,sys,time,re,hashlib
B=Path.cwd();manifest=json.loads((B/sys.argv[1]).read_text());dest=B/'NMN_batch'/manifest['scope'];dest.mkdir(parents=True,exist_ok=True)
for job in manifest['jobs']:
 a=job['attempt'];cfg=B/(a+'-native-config.json');cfg.write_text(json.dumps(job['config'])+'\n')
 start=time.monotonic()
 with (dest/(a+'.stdout.log')).open('w') as out:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(dest/(a+'.time.log')),'python3','NMN_gate.py',str(cfg)],stdout=out,stderr=subprocess.STDOUT)
 raw=(dest/(a+'.stdout.log')).read_text();timing=(dest/(a+'.time.log')).read_text()
 def metric(name):
  m=re.search(re.escape(name)+r':\s*(.*)',timing);return m[1] if m else None
 checks=raw.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0].strip() if 'Failed Checks:' in raw else None
 receipt=dict(attempt=a,kind='kani',module=job['target'],command=['python3','NMN_gate.py',str(cfg)],native_command=job['config']['native_command'],exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms='N/A: Kani',timeout=r.returncode in [124,137] or 'CBMC timed out' in raw,failed_checks=checks,scope=manifest['scope'],actual_kani_invocation=(B/(a+'-kani-submitted.json')).exists())
 (dest/(a+'.receipt.json')).write_text(json.dumps(receipt,indent=1)+'\n')
 print(json.dumps({k:receipt[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','timeout']}),flush=True)
 # Retire a timeout and continue independent variant partitions; never retry it.
 if receipt['timeout']:break
 if not receipt['actual_kani_invocation']:sys.exit(1)
 if job.get('expected')=='pass' and r.returncode!=0:sys.exit(1)
 if job.get('expected')=='fail' and (r.returncode==0 or checks is None or 'unwinding assertion' in checks):sys.exit(1)
