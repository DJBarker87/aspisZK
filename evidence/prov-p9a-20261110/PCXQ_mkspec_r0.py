#!/usr/bin/env python3
"""PCXQ: derive PCXQ_<run>_spec.json for the r0 module from the P4x PCWH_E006 spec: only run name, host paths, source revision/tree hash change.
usage: python3 PCXQ_mkspec_r0.py E006_SPEC RUN"""
import json,sys,re
sys.dont_write_bytecode=True
base,run=sys.argv[1:3]
d=json.load(open(base));old=d['run']
OLDH='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110';NEWH='/home/dombarker/project-offloads/codex-pc-prov-p9a-20261110'
TOOLBIN=OLDH+'/PCWH_T004_out/bin'
def fix(x):
    if x.startswith(TOOLBIN):return x  # tools are read-only by reference in the P4x workspace
    x=x.replace(OLDH,NEWH).replace('PCWH_workspace','PCXQ_workspace').replace(old,run)
    return x
d['charon_command']=[fix(x) for x in d['charon_command']];d['aeneas_command']=[fix(x) for x in d['aeneas_command']]
d['aeneas_command'][d['aeneas_command'].index('-namespace')+1]='PCXQ_r0'
d['aeneas_command'][d['aeneas_command'].index('-subdir')+1]='PCXQ_r0'
d['configuration']['namespace']=['PCXQ_r0']
d.update(run=run,spec_id=run,label='PIN2 r0 module at 271869c946d (public_bytes root, transitive SemanticPublic/private_public/withdrawal_public/semantic)',
 frozen_revision='271869c946d4286db6ee5be784f136599fa8707e',frozen_source_tree_git_hash='ab33a923c2b50acdefe256308ec8aee8018b0be4',derived_from='prov-p4x-20261110/PCWH_E006_spec.json',
 supersedes={'earlier_run':'PCWH_E006 (4bb3b3f)','change':'source revision only'})
d.pop('p1e',None)
json.dump(d,open(run+'_spec.json','w'),indent=1);print(run)
