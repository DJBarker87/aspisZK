#!/usr/bin/env python3
"""Paired opt-in/default frontend regression, with strict sanity checks."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
plan=json.loads(Path(sys.argv[1]).read_text());root=Path(plan['workspace'])
binary=root/'aeneas-associated-types/bin/aeneas'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(binary)==plan['frontend_binary_sha256']
out=Path(plan['case_output']);out.mkdir(parents=True,exist_ok=False);results=[]
for case in plan['cases']:
    target=out/case['name'];target.mkdir()
    command=[str(binary),'-checks','-sequential','-no-progress-bar']
    if case.get('abort',True):command+=['-abort-on-error']
    if case.get('borrow_check',False):command+=['-borrow-check',str(root/case['llbc'])]
    else:command+=['-backend','lean','-namespace',case['namespace'],'-dest',str(target/'generated'),
        '-subdir',case['namespace'],'-split-files','-emit-json',str(root/case['llbc'])]
    env=dict(os.environ,AENEAS_DISABLE_BRANCH_JOIN=case.get('no_join','0'),
        AENEAS_IDENTICAL_ASSOCIATED_TYPES=case['associated_type_matching'])
    started=time.monotonic()
    with (target/'stdout.log').open('w') as stdout,(target/'stderr.log').open('w') as stderr:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(target/'time.log'),*command],
            env=env,stdout=stdout,stderr=stderr,timeout=90)
    timing=(target/'time.log').read_text()
    def metric(name):return int(re.search(re.escape(name)+r':\s*(\d+)',timing)[1])
    actual={p.name:sha(p) for p in (target/'generated'/case.get('namespace','')).glob('*.lean')}
    logs=(target/'stdout.log').read_text()+(target/'stderr.log').read_text()
    passed=result.returncode==case.get('expected_exit',0)
    if 'expected_files' in case:passed=passed and actual==case['expected_files']
    if 'expected_error' in case:passed=passed and case['expected_error'] in logs
    record=dict(case,command=command,env={k:env[k] for k in ['AENEAS_DISABLE_BRANCH_JOIN','AENEAS_IDENTICAL_ASSOCIATED_TYPES']},
        source_revision=plan['source_revision'],features=[],exit_status=result.returncode,
        wall_seconds=time.monotonic()-started,peak_rss_kib=metric('Maximum resident set size (kbytes)'),
        process_swaps=metric('Swaps'),input_llbc_sha256=sha(root/case['llbc']),
        actual_files=actual,frontend_binary_sha256=sha(binary),passed=passed,
        print_axioms='N/A: frontend compatibility/borrow diagnostic, no Lean run')
    (target/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');results.append(record)
    if not passed:break
status=0 if len(results)==len(plan['cases']) and all(r['passed'] for r in results) else 1
(out/'summary.json').write_text(json.dumps(dict(exit_status=status,cases=results,
    harness_sha256=sha(Path(__file__)),scope='Frontend regression, not full library admission'),indent=2)+'\n')
print(json.dumps(dict(exit_status=status,cases=[dict(name=r['name'],passed=r['passed'],exit=r['exit_status']) for r in results])))
raise SystemExit(status)
