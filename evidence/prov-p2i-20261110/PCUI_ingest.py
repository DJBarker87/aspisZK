#!/usr/bin/env python3
"""PCUI_ingest.py: read PCUI_Lnnn receipts; map each printed theorem PRVEq.<ML>.<rel> (ML = module + _i<k> tag) to the definition
<namespace>.<rel> of PCUI_PLAN.json. Output PCUI_PROVED.json {definition: {theorem, receipt, config, fresh_dir, exit}} for scopes with exit 0
and standard-axioms-only theorems, and PCUI_SCOPE_SUMMARY.json."""
import json,glob,os,re,sys
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__))
SET=os.environ.get('PCUI_SET','wb');TYPES=SET in('types','other')
plan=json.load(open(H+{'types':'/PCUI_TYPEPLAN.json','other':'/PCUI_OTHERPLAN.json','wb':'/PCUI_PLAN.json'}[SET]));CFG=json.load(open(H+'/PCUI_EMISSION_CONFIG.json'))
for _p in plan.values():
    for _ps in _p['passes']: _ps['config']=CFG.get(_ps['fresh_dir'].split('/raw/')[0],{}).get('config',_ps['config'])
STD={'propext','Classical.choice','Quot.sound'}
proved={};scopes=[];bad=[]
byml={}
for m,p in plan.items():
    for k,ps in enumerate(p['passes'],1): byml[f'{m}_'+{'types':'t','other':'o','wb':'i'}[SET]+f'{k}']=(m,p,ps)
for rf in sorted(glob.glob(H+'/PCUI_L*/receipt.json')):
    if SET=='types' and not json.load(open(rf))['module'].startswith('PRVEq_bundle_T'): continue
    if SET=='other' and not json.load(open(rf))['module'].startswith('PRVEq_bundle_O'): continue
    if SET=='wb' and json.load(open(rf))['module'].startswith('PRVEq_bundle_'): continue
    r=json.load(open(rf));a=r['attempt'];tgt=r['module'];ok=(r['exit_status']==0) or SET=='other'
    scopes.append(dict(attempt=a,target=tgt,exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],n_axioms=len(r['print_axioms']),source_revision=r['source_revision'],dirty=r['source_tree_dirty']))
    import lzma;_log=lzma.open(os.path.dirname(rf)+'/stdout.log.xz','rt').read()
    _log=re.sub(r'\s*\n\s*',' ',_log)
    lines=re.findall(r"'PRVEq\.[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",_log)
    scopes[-1]['n_axioms']=len(lines)
    for line in lines:
        mm=re.match(r"'PRVEq\.(.+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",line)
        if not mm: continue
        name=mm.group(1);axs={x.strip() for x in (mm.group(2) or '').split(',') if x.strip()}
        if axs-STD: bad.append((a,name,sorted(axs)));continue
        for ml,(m,p,ps) in byml.items():
            if name.startswith(ml+'.'):
                rel=name[len(ml)+1:]
                if rel.endswith('.equiv') and rel[:-6] in ps['only']: rel=rel[:-6]
                if ok and rel in ps['only']:
                    proved[p['namespace']+'.'+rel]=dict(theorem='PRVEq.'+name,module=m,receipt=f'prov-p2i-20261110/{a}/receipt.json',proving_file=f'prov-p2i-20261110/{tgt}.lean',config=ps['config'],fresh_dir=ps['fresh_dir'])
sfx={'types':'_TYPES','other':'_OTHER','wb':''}[SET]
json.dump(proved,open(H+f'/PCUI_PROVED{sfx}.json','w'),indent=1);json.dump(dict(scopes=scopes,nonstandard_axioms=bad),open(H+f'/PCUI_SCOPE_SUMMARY{sfx}.json','w'),indent=1)
need=sum(len(ps['only']) for m,p in plan.items() for ps in p['passes'])
print('proved',len(proved),'of planned',need,'bad',len(bad));
miss=[(m,r) for m,p in plan.items() for ps in p['passes'] for r in ps['only'] if p['namespace']+'.'+r not in proved]
print('missing',len(miss),miss[:40])
