#!/usr/bin/env python3
import argparse,hashlib,json,shutil
from pathlib import Path
from audit_r60_source import audit
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads');src=base/'aspis-r20-r59-partial-dot-20260929-a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
source_root=base/'aspis-r57-lean-src-20260929-a'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
for n in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/circle.rs']:
    if n in m['files']:assert sha(src/n)==m['files'][n]
    copy(src/n,out/'source'/n)
copy(src/'r18-stage.json',out/'source/r18-stage.json')
field=src/'crates/aspis-core/src/field.rs';lean=source_root/'AspisV8R19/InverseChain.lean'
result=audit(field.read_text(),lean.read_text());result.update(field_sha256=sha(field),lean_sha256=sha(lean))
(out/'source/audit.json').write_text(json.dumps(result,indent=2)+'\n')
for folder,names in [('b',['RawReducerNat','RawReducer']),('c',['InverseChain']),('f',['NormInverse'])]:
    for n in names:copy(base/f'aspis-r60-lean-20260929-{folder}'/(n+'.log'),out/'lean'/(n+'.log'))
copy(base/'aspis-r60-lean-20260929-f/metadata.json',out/'lean/metadata.json')
for folder,n in [('b','InverseChain'),('c','NormInverse'),('e','NormInverse')]:
    copy(base/f'aspis-r60-lean-20260929-{folder}'/(n+'.log'),out/f'failures/{folder}-{n}.log')
    records=json.loads((base/f'aspis-r60-lean-20260929-{folder}/metadata.json').read_text())
    (out/f'failures/{folder}-{n}.json').write_text(json.dumps(next(r for r in records if r['target_name']=='AspisV8R19/'+n),indent=2)+'\n')
old=base/'aspis-r17-extracted-cm31.JXBWPZ/AspisV8R17/RawReducer.lean';current=source_root/'AspisV8R17/RawReducer.lean'
assert sha(old)!=sha(current)
(out/'cache-preflight.json').write_text(json.dumps({'old_reducer_sha256':sha(old),'current_reducer_sha256':sha(current),
    'old_unsplit_object_not_reused':True,'old_targets_recompiled':False,'missing_current_dependencies_compiled':['RawReducerNat','RawReducer'],
    'runner_path_typo_before_compilation':True},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
