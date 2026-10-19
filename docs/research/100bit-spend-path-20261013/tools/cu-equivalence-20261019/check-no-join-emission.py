#!/usr/bin/env python3
"""Compare the isolated frontend against pinned small baseline emissions."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
plan=json.loads(Path(sys.argv[1]).read_text())
root=Path(plan['workspace']);binary=root/'aeneas-no-branch-join/bin/aeneas'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(binary)==plan['frontend_binary_sha256']
out=Path(plan['case_output']);out.mkdir(parents=True,exist_ok=False)
results=[]
for case in plan['cases']:
    target=out/case['name'];target.mkdir()
    command=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
        '-namespace',case['namespace'],'-dest',str(target/'generated'),'-subdir',case['namespace'],
        '-split-files','-emit-json',str(root/case['llbc'])]
    env=dict(os.environ,AENEAS_DISABLE_BRANCH_JOIN=case['no_join'])
    started=time.monotonic()
    with (target/'stdout.log').open('w') as stdout,(target/'stderr.log').open('w') as stderr:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(target/'time.log'),*command],
            env=env,stdout=stdout,stderr=stderr)
    timing=(target/'time.log').read_text()
    def metric(label):
        m=re.search(re.escape(label)+r':\s*(\d+)',timing)
        return int(m[1]) if m else None
    actual={p.name:sha(p) for p in (target/'generated'/case['namespace']).glob('*.lean')}
    receipt=dict(case,command=command,source_revision=plan['source_revision'],features=plan['features'],
        exit_status=result.returncode,wall_seconds=time.monotonic()-started,
        peak_rss_kib=metric('Maximum resident set size (kbytes)'),process_swaps=metric('Swaps'),
        input_llbc_sha256=sha(root/case['llbc']),actual_files=actual,
        byte_identical=actual==case['expected_files'],
        print_axioms='N/A: emitted-byte comparison, not a Lean result')
    (target/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    results.append(receipt)
    if result.returncode or not receipt['byte_identical']:break
status=0 if len(results)==len(plan['cases']) and all(r['byte_identical'] and r['exit_status']==0 for r in results) else 1
(out/'summary.json').write_text(json.dumps(dict(exit_status=status,cases=results),indent=2)+'\n')
print(json.dumps(dict(exit_status=status,checks=[dict(name=r['name'],byte_identical=r['byte_identical']) for r in results])))
raise SystemExit(status)
