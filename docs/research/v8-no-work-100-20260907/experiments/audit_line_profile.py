#!/usr/bin/env python3
"""Diagnostic instrumented intervals, never substituted for quiet ELF CU."""
import collections,contextlib,io,json,re,runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/line-profile'
with contextlib.redirect_stdout(io.StringIO()):prior=runpy.run_path(str(EX/'audit_line_norm.py'))
out={'schema':'aspis.research.line-profile.v1','quiet_revision':'074daa2fd0636a577f87bb84075e9ad6fd4f5662','scope':'Four fixed seed1 maximum-body successes; instrumentation/compiler delta is NOT an optimisation.','profiles':{}}
for p in sorted((EV/'line-norm-profile-v1').glob('*.json')):
    x=prior['check'](json.loads(p.read_text()));old=prior['maximum'][p.stem+'-1-success']
    assert x['fixture']['proof_sha256']==old['fixture']['proof_sha256']
    for role in ('pool','registry','token_program'):assert x['artifacts'][role]==old['artifacts'][role]
    assert x['execution']['txv1_declared_compute_unit_limit']==1200000
    points=[];label=None
    for line in x['execution']['logs']:
        if 'Program log: v8:' in line:label=line.split('Program log: ')[1]
        m=re.search(r'Program consumption: (\d+) units remaining',line)
        if m and label:points.append((label,int(m[1])));label=None
    assert len(points)==115 and points[0][0]=='v8:start' and points[-1][0]=='v8:relation-auth-terminal'
    counts=collections.Counter()
    for (_,a),(name,b) in zip(points,points[1:]):assert a>=b;counts[name]+=a-b
    cu=x['execution']['compute_units'];inside=points[0][1]-points[-1][1]
    assert sum(counts.values())==inside
    out['profiles'][p.stem]={'instrumented_cu':cu,'quiet_same_proof_cu':old['execution']['compute_units'],
        'instrumentation_and_compiler_delta':cu-old['execution']['compute_units'],'markers':len(points),
        'intervals_including_instrumentation':dict(counts),'interval_sum':inside,
        'outside_start_to_terminal_including_settlement':cu-inside,
        'artifact':x['artifacts']['selected_verifier'],'proof_sha256':x['fixture']['proof_sha256']}
assert len(out['profiles'])==4
out['build_resources']=prior['prior']['resource'](EV/'line-norm-profile-build-v1.log')
print(json.dumps(out,indent=2))
