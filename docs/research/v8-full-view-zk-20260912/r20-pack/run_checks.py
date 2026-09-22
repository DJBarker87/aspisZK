#!/usr/bin/env python3
"""Compile and run NEW independent checks, without network or dependencies."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, tempfile, time
ROOT=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path);p.add_argument('--sanitize',action='store_true');a=p.parse_args()
compiler=shutil.which('g++')
if not compiler:raise SystemExit('g++ is required')
with tempfile.TemporaryDirectory(prefix='aspis-r20-') as d:
    exe=str(pathlib.Path(d)/'check')
    cmd=[compiler,'-std=c++17','-O2','-DEXTENSION','-Wall','-Wextra','-Werror']
    if a.sanitize:cmd+=['-fsanitize=undefined','-fno-sanitize-recover=all']
    cmd+=[str(ROOT/'tests/check_new.cpp'),'-o',exe]
    t=time.monotonic();build=subprocess.run(cmd,text=True,capture_output=True,check=True)
    compile_seconds=time.monotonic()-t;t=time.monotonic()
    run=subprocess.run([exe],text=True,capture_output=True,check=True,timeout=40)
    report=json.loads(run.stdout)
    report.update(compiler=subprocess.check_output([compiler,'--version'],text=True).splitlines()[0],
                  compile_seconds=round(compile_seconds,3),run_seconds=round(time.monotonic()-t,3),
                  sanitizer=a.sanitize,test_source_sha256=hashlib.sha256((ROOT/'tests/check_new.cpp').read_bytes()).hexdigest())
    if a.output:a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
