import json,re,glob
rem=json.load(open('../prov-p1i-20261110/PCQI_REMAINING.json'))['by_module']
ok={}
STD={'propext','Classical.choice','Quot.sound'}
for r in sorted(glob.glob('PCVH_L0*/receipt.json')):
    d=json.load(open(r))
    if d['exit_status']!=0: continue
    for line in d['print_axioms']:
        m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend)",line,re.S)
        ax=set(a.strip() for a in (m.group(2) or '').replace('\n',' ').split(',') if a.strip())
        if ax<=STD: ok[m.group(1)]=(d['attempt'],d['module'])
proved={};open_=[]
for mod,l in rem.items():
    for x in l:
        if x['class_']!='ON_EMISSION_EXISTS_NOT_COMPARED': continue
        d=x['definition'];hit=None
        for n,(a,mm) in ok.items():
            if mm.startswith('PRVEq_'+mod.replace('.','_')) or True:
                if n.split('.',2)[1].startswith(mod.split('.')[0]) and (n.endswith('.'+d.split('.',1)[-1]) or n.endswith('.'+d.split('.',1)[-1]+'.equiv')) : hit=(n,a)
        (proved.__setitem__(mod+'::'+d,hit) if hit else open_.append(mod+'::'+d))
json.dump(dict(proved=proved,open=open_),open('PCVH_item2.json','w'),indent=1)
print(len(proved),len(open_))
for o in open_: print(' OPEN',o[:110])
for k,v in proved.items(): print(' PROVED',k[:80],v[1])
