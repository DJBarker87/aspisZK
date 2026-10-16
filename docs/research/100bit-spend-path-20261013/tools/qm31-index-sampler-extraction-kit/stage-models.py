#!/usr/bin/env python3
"""Stage the explicit 5/13 existing model-source closure. Never compile."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
REVISION='834ae63ed267c7b8aa7031d2d7f7edaac591114c'
PASS=['SamplerLongDivision','SamplerMachineBounds','SamplerWord','SamplerPass','SamplerWordPass']
DIGITS=PASS+['SamplerAddDigits','SamplerCarry','SamplerDigits','SamplerArithmetic',
             'SamplerAddBridge','SamplerRanking','SamplerNatModel','SamplerRepeatedPass']
PREFIX='docs/research/100bit-spend-path-20261013/lean/'
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def source(path):
    return subprocess.check_output(['git','-C',str(REPO),'show',REVISION+':'+path])

def inputs():
    modules={};files={}
    for name in DIGITS:
        original=PREFIX+name+'.lean'
        raw=source(original)
        imports=[]
        for line in raw.decode().splitlines():
            if line.startswith('import '):
                assert re.fullmatch(r'import [A-Za-z0-9_. ]+',line)
                imports.extend(line[7:].split())
            elif line.strip():break
        module='R1'+name
        files[module+'.lean']=raw
        modules[module]={'source':original,'source_sha256':sha(raw),
                         'git_blob':subprocess.check_output(['git','-C',str(REPO),'rev-parse',REVISION+':'+original],text=True).strip(),
                         'source_revision':REVISION,'imports':imports,'role':'existing sampler model; compile only',
                         'stage_as':module+'.lean','prior_object_selected':False,
                         'axiom_requests':re.findall(r'^#print axioms (.+)$',raw.decode(),re.M)}
    order=['R1'+n for n in DIGITS]
    for index,name in enumerate(order):
        for dep in modules[name]['imports']:
            if dep in modules:assert order.index(dep)<index
            else:assert dep.startswith(('Mathlib.','Lean.','Init.','Std.')),dep
    manifest={'format':2,'source_base':REVISION,'state':'STAGED_ONLY; no new Lean job or object attestation',
              'target_toolchain':'leanprover/lean4:v4.32.0','modules':modules,'topological_order':order,
              'groups':{'pass':{'targets':['R1SamplerWordPass'],'order':['R1'+n for n in PASS]},
                        'digits':{'targets':['R1SamplerRepeatedPass'],'order':order}},
              'external_import_boundary':sorted({d for item in modules.values() for d in item['imports'] if d not in modules}),
              'object_policy':'Only own new 4.32 objects and exact R17 external snapshot; no 4.31 inputs/package build',
              'excluded':'The 64-new-module SourceSamplerByteRank/legacy sampler closure is not staged or authorized here.',
              'generator_sha256':sha(Path(__file__).read_bytes())}
    files['SOURCE-MANIFEST.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
    return files

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('workspace',type=Path)
    p.add_argument('--check',action='store_true')
    a=p.parse_args();target=a.workspace/'sources';files=inputs()
    if not a.check:target.mkdir(parents=True,exist_ok=False)
    for name,raw in files.items():
        path=target/name
        if a.check:assert path.read_bytes()==raw,path
        else:path.write_bytes(raw)
    assert {str(p.relative_to(target)) for p in target.rglob('*') if p.is_file()}==set(files)
    print('PASS: explicit 5/13-module source staging; no Lean executed')

if __name__=='__main__':main()
