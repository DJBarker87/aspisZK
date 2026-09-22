#!/usr/bin/env python3
"""Fail closed: this is a benchmark-evidence gate, NOT a security theorem.
Input is a JSON receipt with artifact IDs and complete-primary runner results.
"""
import argparse,json,pathlib,re
p=argparse.ArgumentParser();p.add_argument('receipt',type=pathlib.Path);a=p.parse_args();r=json.loads(a.receipt.read_text())
errors=[]
for key in ['commit_sha','elf_sha256']:
    n=40 if key=='commit_sha' else 64
    if not re.fullmatch('[0-9a-f]{%d}'%n,str(r.get(key,''))):errors.append('missing/invalid '+key)
if r.get('scope')!='complete-primary-verifier':errors.append('not a complete-primary verifier measurement')
if r.get('instrumented') is not False:errors.append('un-instrumented acceptance run required')
if r.get('heap_bytes')!=262144:errors.append('baseline heap changed')
if r.get('same_profile') is not True:errors.append('R20 exact-profile gate expects unchanged R19 profile')
honest={}; negatives=0
for case in r.get('cases',[]):
    if case.get('cu_limit')!=1_000_000:errors.append('actual 1,000,000 CU cap required')
    cu=case.get('cu');
    if not isinstance(cu,int) or cu<0 or cu>=1_000_000:errors.append('missing or over-target CU')
    if case.get('complete') is not True:errors.append('incomplete execution')
    if case.get('resource_failure') is not False:errors.append('resource exhaustion is not checked rejection')
    if case.get('kind')=='honest':
        if case.get('accepted') is not True:errors.append('honest input did not accept')
        h=case.get('fixture_sha256','')
        if not re.fullmatch('[0-9a-f]{64}',h):errors.append('invalid fixture hash')
        honest[h]=case
    elif case.get('kind')=='negative':
        negatives+=1
        if case.get('accepted') is not False:errors.append('negative input accepted')
if len(honest)<2:errors.append('at least two distinct genuine source fixtures required')
if negatives<1:errors.append('checked negative controls required')
print(json.dumps({'sub_1m_benchmark_pass':not errors,'errors':errors,
                  'universal_resource_bound_proved':False,'privacy_proved':False,'soundness_proved':False},indent=2))
raise SystemExit(bool(errors))
