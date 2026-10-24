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
REVISIONS = {'stability':'f7b90c82300c8a2409625fefb5dc529db6547f9c','available':'fbe04424e7553d9b0844ae19c2206b15cf3dd831',
             'actual':'5756082d85e4d6784de4566059d6a9845604342a'}
SPECS = {
    'candidate':('available','tools/resource-available-20261024/ResourceAvailable_candidate.py'),
    'go':('available','tools/resource-available-20261024/ResourceAvailable_go.py'),
    'identity':('actual','tools/resource-stat-20261024/ResourceStat_go.py'),
    'inventory':('actual','tools/resource-stat-20261024/baseline/reservation_base.py'),
    'policy':('stability','tools/resource-stability-20261025/ResourceStability_evaluator.py'),
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
    path=HERE/'ResourceStableGO_reviewed.json'
    data=json.loads(path.read_bytes()) if path.exists() else bundle()
    if set(data)!=set(SPECS):raise ValueError('reviewed source set drift')
    for key,(rev,path) in SPECS.items():
        entry=data[key]
        if entry['revision']!=REVISIONS[rev] or entry['path']!=path or digest(entry['source'].encode())!={k:entry[k] for k in ('sha256','size')}:
            raise ValueError('reviewed source pin drift')
    validate_bundle(data)
    return data

def functions(source,names,env):
    tree=ast.parse(source)
    selected=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name in names]
    if {n.name for n in selected}!=set(names):raise ValueError('missing reviewed function')
    exec(compile(ast.Module(body=selected,type_ignores=[]),'ResourceStableGO-reviewed-functions','exec'),env)
    return env

def load(data=None):
    data=load_bundle() if data is None else data
    validate_bundle(data)
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
    aliases=types.ModuleType('ResourceStability_sources')
    aliases.c=candidate
    aliases.go=types.SimpleNamespace(**go)
    previous=sys.modules.get('ResourceStability_sources')
    sys.modules['ResourceStability_sources']=aliases
    try:
        policy=types.ModuleType('ResourceStableGO_reviewed_policy')
        exec(compile(data['policy']['source'],data['policy']['path'],'exec'),policy.__dict__)
    finally:
        if previous is None:sys.modules.pop('ResourceStability_sources',None)
        else:sys.modules['ResourceStability_sources']=previous
    return candidate,go,identity,inventory,policy

PINS = {'candidate': {'sha256': 'f5dfc0fe475d27fa08beee10a3f8b6badbf08c6d9ce7819b600d3b5cb3562aa6', 'size': 18032}, 'go': {'sha256': '1f207247cdf947ec6c1d0a9b6fbf8126caae1f9b0373915b1d11df537199a574', 'size': 7675}, 'identity': {'sha256': '0ff959fd4e01414fa7748c2598a19cdb34dd24b38ba14ac85e2294f282429000', 'size': 15649}, 'inventory': {'sha256': 'a5943cb407b28f4807cd20986d37b31ecd5eae103781a07dc7e9affbb144afd2', 'size': 4713}, 'fixtures': {'sha256': 'c453bc3ea9423de7054b36f196805196c0f149c09a9c99212f2e8bd9b618621e', 'size': 12809}, 'policy': {'sha256': '8dfffb421e33df0cfd43e0b3c43112f5d9ea34a65bf83da8e60adff82ab73813', 'size': 7448}}

def validate_bundle(data):
    if set(data)!=set(SPECS):raise ValueError('reviewed source set drift')
    for key,(rev,path) in SPECS.items():
        item=data[key]
        if item['revision']!=REVISIONS[rev] or item['path']!=path or digest(item['source'].encode())!=PINS[key] or {k:item[k] for k in ('sha256','size')}!=PINS[key]:
            raise ValueError('reviewed immutable source pin drift: '+key)
