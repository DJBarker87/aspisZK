#!/usr/bin/env python3
"""PCUI_typeshapes.py: classify the TEXT_IDENTICAL_ONLY / TEXT_ONLY_NOT_COMPARED Types records (non-cut modules) by declaration shape of the gate text.
Output PCUI_TYPESHAPES.json."""
import json,re,subprocess,sys,os,collections
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(H);REPO=os.path.dirname(os.path.dirname(EV))
sys.path.insert(0,EV+'/prov-p2h-20261109');import PCUH_gen_equalities as G
P=json.load(open(EV+'/prov-p6c-20261109/PCXB_PROVENANCE.json'));PART=json.load(open(EV+'/prov-p5-20261109/PCT_PARTITION.json'))
ns=json.load(open(EV+'/prov-p6c-20261109/PCXB_NOSOURCE.json'));so=json.load(open(EV+'/prov-p6c-20261109/PCXB_SECOND_TIER_OPEN.json'))
cut=set()
for k in list(ns['modules'])+list(so['modules']): cut.add(k if isinstance(k,str) else k.get('module'))
def gitshow(p):
    r=subprocess.run(['git','-C',REPO,'show','research:'+p],capture_output=True,text=True);return r.stdout if r.returncode==0 else None
out={};cnt=collections.Counter()
for mn,m in P['modules'].items():
    if mn in cut: continue
    todo=[(dn,df) for dn,df in m['definitions'].items() if df['in_splitB_cone'] and df['status']=='OPEN' and (df.get('open_reason') or '').startswith(('TEXT_IDENTICAL_ONLY','TEXT_ONLY','TEXT_DIFFERS'))]
    if not todo: continue
    txt=None
    for c in PART['modules'].get(mn,{}).get('candidates',[]):
        for p in c['paths']:
            txt=gitshow(p)
            if txt: break
        if txt: break
    if not txt:
        for dn,df in todo: out[dn]=dict(module=mn,shape='NO_GATE_SOURCE');cnt['NO_GATE_SOURCE']+=1
        continue
    nsm=re.findall(r'(?m)^namespace\s+(\S+)',txt);gns=nsm[0] if nsm else ''
    bl={b['name']:b for b in G.parse_blocks(txt) if b['kind']=='decl'}
    for dn,df in todo:
        rel=dn[len(gns)+1:] if dn.startswith(gns+'.') else dn
        b=bl.get(rel)
        if not b: out[dn]=dict(module=mn,shape='NOT_FOUND');cnt['NOT_FOUND']+=1;continue
        body=b['body'];k=b['dkind']
        if k=='inductive':
            ctors=re.findall(r'(?m)^\s*\|\s*(\S+)(.*)$',body)
            sh='ENUM' if all(not c[1].strip() or c[1].strip().startswith(('=>',':')) and False for c in ctors) else 'INDUCTIVE_ARGS'
            if all(not re.search(r'[A-Za-z(]',c[1]) for c in ctors): sh='ENUM'
        elif k=='structure': sh='STRUCTURE'
        else: sh='DEF_'+k
        declared={x for x in bl if bl[x]['dkind'] in ('inductive','structure')}
        toks=set(G.lean_ident_tokens(body.split(':=',1)[-1] if k in('def','abbrev') else body))-{rel}
        refs=sorted(toks&declared)
        out[dn]=dict(module=mn,shape=sh,refs=refs,dkind=k,params=bool(re.match(r'\s*\w+\s+[^\s:]*\s*\(',body.split('\n')[0])) );cnt[sh]+=1
json.dump(out,open(H+'/PCUI_TYPESHAPES.json','w'),indent=1);print(cnt)
