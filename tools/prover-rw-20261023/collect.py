#!/usr/bin/env python3
"""Collect textual receipts and metadata only; never proof/ELF/key artifacts."""
from pathlib import Path
import subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/continuation';E.mkdir(exist_ok=True)
host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023'
for name,root in [('candidate','src'),('baseline','baseline-src')]:
 dest=E/'receipts'/name;dest.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-a','--include=*/','--include=receipt.json','--include=preflight.json','--include=stdout.log','--include=stderr.log','--include=time.log','--exclude=*',host+':'+H+'/'+root+'/receipts/',str(dest)+'/'],check=True)
for file in ['allocation-comparison.json','elf-byte-comparison.json','smoke-comparison.json','smoke-binaries.json','focused-paired-001-comparison.json','focused-paired-001-binaries.json','tool-versions.json','phase-paired-002-comparison.json','phase-paired-002-binaries.json','external-call-inventory.json','all-classes-paired-001-comparison.json','all-classes-paired-001-binaries.json','elf-byte-comparison-proverw002.json','oracle-paired-001-comparison.json','oracle-paired-001-binaries.json']:
 subprocess.run(['rsync','-a',host+':'+H+'/'+file,str(E/file)],check=True)
for name in ['semantic-001','pipeline-001']:
 subprocess.run(['rsync','-a',host+':'+H+'/interleaved-'+name+'/comparison.json',str(E/('interleaved-'+name+'.json'))],check=True)
subprocess.run(['rsync','-a',host+':'+H+'/src/elf-identities.json',str(E/'elf-identities.json')],check=True)
for root,pattern in [('src','reservation-*.json'),('baseline-src','reservation-*.json')]:
 dest=E/'reservations'/root;dest.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-a',host+':'+H+'/'+root+'/'+pattern,str(dest)+'/'],check=True)
