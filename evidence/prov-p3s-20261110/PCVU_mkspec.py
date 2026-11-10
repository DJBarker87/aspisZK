import json,sys,os
# usage: [BASE=E002] PCVU_mkspec.py RUN label ns overflow(ON|OFF) root1 root2 ...   (BASE: E001 aspis-core r0, E002 cost-probe)
run,label,ns,ov=sys.argv[1:5];roots=sys.argv[5:]
base=os.environ.get('BASE','E001')
d=json.load(open('../prov-p3r-20261110/PCVS_%s_spec.json'%base))
oldns=d['configuration']['namespace'][0]
s=json.dumps(d).replace('PCVS_'+base,run).replace('codex-pc-prov-p3r-20261110','codex-pc-prov-p3s-20261110').replace(oldns,ns).replace('PCVS_','PCVU_')
d=json.loads(s)
def fix(cmd):
    out=[];i=0;done=False
    while i<len(cmd):
        if cmd[i]=='--start-from':
            if not done:
                for r in roots: out+=['--start-from',r]
                done=True
            i+=2;continue
        out.append(cmd[i]);i+=1
    return out
for k in (d,d['configuration']):
    k['charon_command']=fix(k['charon_command']);k['roots']=roots;k['label']=label
d['derived_from']='prov-p3r-20261110/PCVS_%s_spec.json (roots/namespace changed); overflow %s'%(base,ov)
if ov=='OFF':
    d['extra_env']={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false'}
    d['configuration_overflow_checks']='OFF'
json.dump(d,open(run+'_spec.json','w'),indent=1)
print(run,[x for x in d['charon_command'] if x.startswith('crate')])
