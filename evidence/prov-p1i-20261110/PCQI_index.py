#!/usr/bin/env python3
"""index existing ON emissions (spec extra_env overflow ON) by declared Lean name; match against the 325 NO_FRESH gate definitions"""
import json,glob,re,os,sys
sys.dont_write_bytecode=True
ev=os.path.abspath('.')
idx={}
for sp in glob.glob(ev+'/*/*_spec.json')+glob.glob(ev+'/*/*/*_spec.json'):
    try:s=json.load(open(sp))
    except Exception: continue
    env=s.get('extra_env') or {}
    on=env.get('CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')=='true'
    run=s.get('run');d=os.path.dirname(sp)
    em=os.path.join(d,run+'_emitted/raw')
    if not os.path.isdir(em): continue
    for f in glob.glob(em+'/*/Funs.lean')+glob.glob(em+'/*/Types.lean'):
        t=open(f).read()
        for m in re.finditer(r'(?m)^(?:@\[[^\]]*\]\s*)?(?:def|structure|inductive|abbrev)\s+([^\s(:{\[]+)',t):
            idx.setdefault(m.group(1),[]).append((run,'ON' if on else 'OFF',os.path.relpath(os.path.dirname(f),ev)))
json.dump(idx,open('/tmp/idx.json','w'))
want=json.load(open('/tmp/nofresh325.json'))
out={}
for mod,defs in want.items():
    for d in defs:
        parts=d.split('.');hit=None
        for i in range(0,len(parts)-0):
            suf='.'.join(parts[i:])
            if suf in idx:
                hit=(suf,idx[suf]);break
        out.setdefault(mod,[]).append((d,hit))
for mod,l in out.items():
    h=[x for x in l if x[1]]
    print(mod,len(l),'matched',len(h))
    for d,hit in h[:3]: print('   ',d,'->',[(r,c) for r,c,_ in hit[1]][:4])
