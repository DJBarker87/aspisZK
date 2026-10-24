"""Sealed immutable source loading; no old runner/main or live worktree reads."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REVISIONS = {'available':'fbe04424e7553d9b0844ae19c2206b15cf3dd831',
             'actual':'5756082d85e4d6784de4566059d6a9845604342a'}
SPECS = {
    'candidate':('available','tools/resource-available-20261024/ResourceAvailable_candidate.py'),
    'go':('available','tools/resource-available-20261024/ResourceAvailable_go.py'),
    'identity':('actual','tools/resource-stat-20261024/ResourceStat_go.py'),
    'inventory':('actual','tools/resource-stat-20261024/baseline/reservation_base.py'),
    'fixtures':('available','tools/resource-available-20261024/ResourceAvailable_tests.py'),
}

def digest(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))

def bundle():
    sources={}
    for key,(rev,path) in SPECS.items():
        raw=subprocess.check_output(['git','show',REVISIONS[rev]+':'+path],cwd=ROOT)
        sources[key]=dict(revision=REVISIONS[rev],path=path,source=raw.decode(),**digest(raw))
    return sources

def load_bundle():
    path=HERE/'ResourceAdmit_reviewed.json'
    data=json.loads(path.read_bytes()) if path.exists() else bundle()
    if set(data)!=set(SPECS):raise ValueError('reviewed source set drift')
    for key,(rev,path) in SPECS.items():
        entry=data[key]
        if entry['revision']!=REVISIONS[rev] or entry['path']!=path or digest(entry['source'].encode())!={k:entry[k] for k in ('sha256','size')}:
            raise ValueError('reviewed source pin drift')
    return data

def functions(source,names,env):
    tree=ast.parse(source)
    selected=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name in names]
    if {n.name for n in selected}!=set(names):raise ValueError('missing reviewed function')
    exec(compile(ast.Module(body=selected,type_ignores=[]),'ResourceAdmit-reviewed-functions','exec'),env)
    return env

def load(data=None):
    data=load_bundle() if data is None else data
    candidate=types.ModuleType('ResourceAvailable_candidate')
    exec(compile(data['candidate']['source'],data['candidate']['path'],'exec'),candidate.__dict__)
    previous=sys.modules.get('ResourceAvailable_candidate')
    sys.modules['ResourceAvailable_candidate']=candidate
    try:
        go={}
        exec(compile(data['go']['source'],data['go']['path'],'exec'),go)
    finally:
        if previous is None:sys.modules.pop('ResourceAvailable_candidate',None)
        else:sys.modules['ResourceAvailable_candidate']=previous
    import os
    from pathlib import PurePosixPath
    identity=functions(data['identity']['source'],['self_observation','scan_bound'],
                       dict(base=candidate.__dict__,os=os,Path=Path,PurePosixPath=PurePosixPath,hashlib=hashlib))
    inventory=functions(data['inventory']['source'],['number','inventory'],dict(os=os,Path=Path))
    return candidate,go,identity,inventory
