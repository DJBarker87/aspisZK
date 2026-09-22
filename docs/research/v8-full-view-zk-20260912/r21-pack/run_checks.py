#!/usr/bin/env python3
"""Compile/replay arithmetic experiments; NOT a source or SBF test runner."""
import argparse,json,subprocess,tempfile
from pathlib import Path
root=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ranks',action='store_true');a=p.parse_args()
subprocess.run(['python3',str(root/'tools/generate_cycles.py')],check=True)
results={}
with tempfile.TemporaryDirectory(prefix='aspis-r21-') as td:
    jobs=[('controls','check_cycles.cpp',True)]
    if a.ranks: jobs += [('rank_base','screen_cycles.cpp',False),('rank_qm31','screen_cycles.cpp',True)]
    for name,source,ext in jobs:
        output=str(Path(td)/name)
        cmd=['g++','-O2','-std=c++17','-fsanitize=undefined','-fno-sanitize-recover=all']
        if ext:cmd+=['-DEXTENSION']
        subprocess.run(cmd+[str(root/'tests'/source),'-o',output],check=True)
        run=subprocess.run([output],check=True,text=True,capture_output=True)
        results[name]=[json.loads(line) for line in run.stdout.splitlines()]
        print(run.stdout,end='')
(root/'evidence/local_replay.json').write_text(json.dumps(results,indent=2)+'\n')
