#!/usr/bin/env python3
"""Isolated formatting-only Aeneas candidate. No translation-rule changes."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-formatter-tool-v1';P.mkdir(exist_ok=False)
source=H/'s1-collapse-tool-recover-v2/source/src';shutil.copytree(source,P/'src',symlinks=True)
f=P/'src/Translate.ml';before=f.read_text();assert before.count('Format.pp_set_margin fmt 80;')==1
f.write_text(before.replace('Format.pp_set_margin fmt 80;','Format.pp_set_margin fmt 1000;',1))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(P/'formatter-only.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original_source=str(source),original_sha256=hashlib.sha256(before.encode()).hexdigest(),candidate_sha256=sha(f),only_change='Format.pp_set_margin fmt 80 ->1000',qualification=__doc__),indent=2)+'\n')
tag='s6-formatter-tool-build-v1';subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
os.chdir(P/'src');cmd=['/usr/bin/opam','exec','--','dune','build','-j','1','main.exe']
(H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,cwd=str(P/'src'),change=sha(f),expected_time='Incremental optimized OCaml formatter candidate rebuild; only printing margin changed, cached compiler objects copied.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Incremental formatter-only tool build, one job','--','timeout','120',*cmd]))
