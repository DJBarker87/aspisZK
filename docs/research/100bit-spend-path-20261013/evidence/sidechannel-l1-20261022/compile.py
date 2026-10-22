#!/usr/bin/env python3
"""Focused env-J attempt with pinned source/dependencies and raw receipts."""
import hashlib, json, re, shlex, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
REMOTE='/home/dombarker/project-offloads/aspis-joint-20261019'
EVIDENCE='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
LAUNCH='/home/dombarker/project-offloads/codex-cx-l1-coupling-20261022/run-joint.sh'
def ssh(cmd):
    return subprocess.check_output(['ssh',HOST,cmd],text=True)
def main():
    attempt=int(sys.argv[1]); module=sys.argv[2]
    assert 9800 <= attempt <= 9899 and module.startswith('SideChannel')
    src=Path.cwd()/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{module}.lean'
    target=f'R1Z/{module}'
    ssh(f'test ! -e {EVIDENCE}/out-{attempt}.log')
    data=src.read_bytes(); imports=re.findall(r'^import (\S+)',data.decode(),re.M)
    deps=json.loads(ssh('python3 -c '+shlex.quote(
        'import hashlib,json,pathlib; base=pathlib.Path('+repr(REMOTE+'/objects')+'); '
        'names='+repr(imports)+'; print(json.dumps({n:hashlib.sha256((base/(n.replace(".","/")+".olean")).read_bytes()).hexdigest() for n in names}))')))
    fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
    subprocess.run(['scp','-q',str(src),f'{HOST}:{REMOTE}/sources/{target}.lean'],check=True)
    (HERE/'sources').mkdir(exist_ok=True)
    (HERE/'sources'/f'{attempt}-{module}.lean.txt').write_bytes(data)
    meta={'attempt':attempt,'module':target,'source_sha256':hashlib.sha256(data).hexdigest(),
          'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
          'source_note':'exact candidate bytes in sources snapshot; may be uncommitted',
          'deps':deps,'deps_fingerprint':fingerprint,'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},
          'command':f'sh {LAUNCH} {attempt} {target} J 7000 8 {fingerprint}'}
    result=subprocess.run(['ssh',HOST,meta['command']],text=True,capture_output=True)
    (HERE/f'launcher-{attempt}.log').write_text(result.stdout+result.stderr)
    for kind in ('out','time','sha'):
        suffix='txt' if kind=='sha' else 'log'
        subprocess.run(['scp','-q',f'{HOST}:{EVIDENCE}/{kind}-{attempt}.{suffix}',str(HERE)],check=True)
    log=(HERE/f'out-{attempt}.log').read_text(); timing=(HERE/f'time-{attempt}.log').read_text()
    meta['exit']=int(re.search(r'^exit=(\d+)',log,re.M)[1])
    meta['axioms_lines']=[x for x in log.splitlines() if 'axioms' in x or x.startswith(' Classical.') or x.startswith(' Quot.')]
    meta['errors']=[x for x in log.splitlines() if 'error:' in x or 'error(' in x]
    meta['time_fields']={line.strip().split(': ',1)[0]:line.strip().split(': ',1)[1] for line in timing.splitlines() if ': ' in line}
    (HERE/f'attempt-{attempt}.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(result.stdout[-6000:]); print(result.stderr)
    return meta['exit']
if __name__=='__main__': sys.exit(main())
