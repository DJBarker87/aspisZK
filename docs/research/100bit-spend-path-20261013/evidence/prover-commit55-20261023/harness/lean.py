#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
H='/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023'
m,a=sys.argv[1:];src=L/(m.replace('.','/')+'.lean')
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
subprocess.run(['ssh','dombarker@100.108.41.90','mkdir','-p',H+'/sources/'+str(src.relative_to(L).parent)],check=True)
subprocess.run(['rsync','-a',str(src),'dombarker@100.108.41.90:'+H+'/sources/'+str(src.relative_to(L))],check=True)
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3',H+'/build/compile-proof.py',m,a,rev])
subprocess.run(['rsync','-a','--include=J'+a+'.*','--exclude=*','dombarker@100.108.41.90:'+H+'/proof-evidence/',str(E/'lean')+'/'],check=True)
sys.exit(p.returncode)
