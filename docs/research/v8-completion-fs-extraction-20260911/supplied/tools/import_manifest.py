#!/usr/bin/env python3
"""Resolve an explicit first-party Lean import closure without using .olean files.

Each --root is a Lean import root. Ambiguous resolution FAILS rather than
silently selecting an older overlay. Third-party prefixes require explicit
--external names and are disclosed boundaries, not independently rebuilt code.
"""
from __future__ import annotations
import argparse,hashlib,json,re,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from source_audit import strip_lean_comments


def manifest(roots:list[Path],targets:list[str],external:list[str])->dict:
    found={};missing=[];ambiguous=[];active=set();done=set();order=[]
    def visit(module):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",module):
            raise ValueError('unsupported/unsafe module name: '+module)
        if module in done:return
        if module in active:raise ValueError('import cycle: '+module)
        if any(module==p or module.startswith(p+'.') for p in external):
            found[module]={'status':'EXTERNAL_PIN_REQUIRED'};done.add(module);return
        rel=Path(*module.split('.')).with_suffix('.lean')
        candidates=[r/rel for r in roots if (r/rel).is_file()]
        # Even byte-identical duplicates must be reconciled; path precedence matters.
        if not candidates:missing.append(module);done.add(module);return
        if len(candidates)>1:ambiguous.append({'module':module,'paths':[str(p) for p in candidates]});done.add(module);return
        path=candidates[0];code=strip_lean_comments(path.read_text())
        imports=[]
        for line in code.splitlines():
            line=line.strip()
            if line.startswith('import '):imports.extend(line[7:].split())
        active.add(module)
        for dep in imports:visit(dep)
        active.remove(module);done.add(module);order.append(module)
        found[module]={'path':str(path.resolve()),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                       'imports':imports,'status':'SOURCE_RESOLVED_NOT_BUILT'}
    for target in targets:visit(target)
    return {'status':'RESOLVED_NOT_BUILT' if not missing and not ambiguous else 'BLOCKED',
            'targets':targets,'roots':[str(r.resolve()) for r in roots],'modules':found,
            'topological_order':order,'missing':missing,'ambiguous':ambiguous,
            'external_prefixes':external}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,action='append',required=True)
    p.add_argument('--target',action='append',required=True);p.add_argument('--external',action='append',default=[])
    p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    try:r=manifest(a.root,a.target,a.external)
    except (ValueError,OSError) as e:r={'status':'BLOCKED','reason':str(e)}
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(r['status']);raise SystemExit(0 if r['status']=='RESOLVED_NOT_BUILT' else 1)
