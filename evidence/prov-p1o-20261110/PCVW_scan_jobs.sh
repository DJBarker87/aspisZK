#!/bin/bash
# usage: bash PCVW_scan_jobs.sh OUT.json   scans every Stream C extraction spec reachable from research and the codex/pc-prov-* branches (read-only git) for non-pinned cargo jobs / -Zthreads
cd "$(git rev-parse --show-toplevel)"
python3 -B - "$1" <<'PY'
import subprocess,json,sys,re
def g(*a):return subprocess.run(['git',*a],capture_output=True,text=True).stdout
refs=['research']+[l.strip() for l in g('for-each-ref','--format=%(refname:short)','refs/heads/codex/pc-prov-*').splitlines()]
seen={};rows=[];nojobs=[]
for ref in refs:
    for path in g('ls-tree','-r','--name-only',ref,'--','evidence').splitlines():
        if not re.search(r'/[A-Z]{3,4}[A-Z]?_[EW]\d{3}_spec\.json$',path) or '/prov-p' not in path:continue
        blob=g('rev-parse',ref+':'+path).strip()
        if blob in seen:continue
        seen[blob]=1
        try:d=json.loads(g('show',ref+':'+path))
        except Exception:continue
        c=d.get('charon_command') or []
        raw=g('show',ref+':'+path)
        envjobs=re.findall(r'"CARGO_BUILD_JOBS": "(\d+)"',raw)
        if '--jobs' not in c and not envjobs:
            nojobs.append(dict(path=path,ref=ref,run=d.get('run')));continue
        jobs=c[c.index('--jobs')+1] if '--jobs' in c else 'env:'+envjobs[-1]
        rf=(d.get('extra_env') or {}).get('RUSTFLAGS','')
        m=re.findall(r'-Zthreads=(\d+)',rf)
        threads=m[-1] if m else None
        # effective threads: the stager sets -Zthreads=1 first; an appended -Zthreads wins
        eff=threads if threads else '1 (stager default)'
        pinned=(jobs in ('1','env:1') and eff.startswith('1'))
        rows.append(dict(path=path,ref=ref,blob=blob,run=d.get('run'),jobs=jobs,zthreads_appended=threads,effective_threads=eff,pinned=pinned,
                         manifest=c[c.index('--manifest-path')+1].split('/')[-2] if '--manifest-path' in c else None))
rows.sort(key=lambda r:r['path'])
out=dict(schema='PCVW_JOBS_SCAN/1',n_specs=len(rows),non_pinned=[r for r in rows if not r['pinned']],pinned_count=sum(r['pinned'] for r in rows),specs_without_a_jobs_setting=len(nojobs),specs_without_a_jobs_setting_examples=nojobs[:5])
json.dump(out,open(sys.argv[1],'w'),indent=1)
print(len(rows),'specs;',len(out['non_pinned']),'non-pinned')
for r in out['non_pinned']:print(r['run'],r['jobs'],r['zthreads_appended'],r['ref'],r['path'].split('/')[1])
PY
