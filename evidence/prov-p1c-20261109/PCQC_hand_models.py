#!/usr/bin/env python3
"""PCQC_HAND_MODELS.json (lead addendum), over the overflow-checks-on runs of P1c plus the carried P1a PCQ_E037-E040: for every covered gate module of a successful P1a run, list each external
name (axiom/opaque in the fresh emission) together with the gate's definition of that name (file + exact text, read from
research via git show) and its classification. RECORD ONLY: no trust rows are added or proposed.
gate_form: 'axiom' = gate also keeps an external/opaque declaration; 'def/abbrev/instance/structure/inductive' = the
gate side defines it concretely (hand-written model); 'NOT_FOUND' = no gate declaration of that name in the searched
files (searched: the module's candidate files and sibling *External*.lean / Types files in the same directory)."""
import json,re,subprocess,sys
from pathlib import Path
E=Path(__file__).resolve().parent;EV=E.parent;ZK='/Users/dominic/ZK/.worktrees/pc-prov-p1c'
PARTS={'A':json.loads((EV/'prov-p1a-20261109/PCQ_PARTITION.json').read_text())['modules'],'B':json.loads((EV/'prov-p1b-20261109/PCQ_PARTITION.json').read_text())['modules']}
LOCK=subprocess.run(['git','-C',ZK,'show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],capture_output=True,text=True).stdout
def crate_ver(first):
    cands=[first.replace('_','-'),first]
    for c in cands:
        m=re.search(r'\[\[package\]\]\nname = "%s"\nversion = "([^"]+)"'%re.escape(c),LOCK)
        if m:return '%s %s (Cargo.lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387)'%(c,m.group(1))
    return None
def pinned(name):
    first=name.split('.')[0]
    if first in('core','alloc','std'):return 'Rust %s library, rustc nightly-2026-06-01 sysroot (tool pin PCQ_*_PINS.json; no crate version)'%first
    return crate_ver(first) or 'workspace/unknown: %s'%first
def git_show(path):
    r=subprocess.run(['git','-C',ZK,'show','research:'+path],capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
def ls(dirp):
    r=subprocess.run(['git','-C',ZK,'ls-tree','--name-only','research',dirp.rstrip('/')+'/'],capture_output=True,text=True)
    return [x for x in r.stdout.split('\n') if x]
FRESH=re.compile(r"^((?:@\[[^\n]*\]\n)?)(axiom|opaque)\s+([^\s:(\[{]+)(.*?)(?=\n\n|\n/--|\Z)",re.M|re.S)
def fresh_externals(run,d):
    out={}
    for f in sorted((d/(run+'_emitted/raw')).glob('*/*.lean')):
        t=f.read_text()
        for pre,kind,name,rest in FRESH.findall(t):
            out[name]=dict(file=str(f.relative_to(EV)),text=(pre+kind+' '+name+rest).strip())
    return out
GATE=re.compile(r"^(?:@\[[^\n]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(def|abbrev|instance|axiom|opaque|structure|inductive|theorem)\s+(\S+)",re.M)
def search_gate(files,ext):
    last=ext.split('.')
    hits=[]
    for path,txt in files.items():
        if txt is None:continue
        lines=txt.split('\n')
        for m in GATE.finditer(txt):
            n=m.group(2)
            if n==ext or n.endswith('.'+ext) or ext.endswith('.'+n.split('.',1)[-1]) and n.split('.',1)[-1]==ext.split('.',1)[-1] and False:
                ln=txt[:m.start()].count('\n');end=ln
                while end<len(lines) and (end==ln or lines[end].strip()!=''):end+=1
                hits.append(dict(file=path,line=ln+1,gate_name=n,form=m.group(1),text='\n'.join(lines[ln:min(end,ln+40)])))
    return hits
cov=json.loads((E/'PCQC_COVERAGE.json').read_text())
res=dict(schema=1,target_established=False,note='Record only; no trust row added or proposed (lead addendum). Name match is exact or suffix after the gate namespace. Covers P1c overflow-on runs and the carried P1a PCQ_E037-E040.',entries=[])
def rundir(run):
    return E if run.startswith('PCQC_') else EV/'prov-p1a-20261109'
for sid,e in cov['specs'].items():
    runs=sorted({d['run'] for d in e['definitions'].values() if d['status']!='MISSING'})
    part=PARTS['B'] if sid in [f'S0{n}' for n in range(15,23)] else PARTS['A']
    for run in runs:
        ext=fresh_externals(run,rundir(run))
        spec_run=json.loads((rundir(run)/(run+'_spec.json')).read_text())
        opq={o.replace('crate::','').replace('::','.') for o in spec_run['configuration'].get('opaque',[])}
        for mod in (e.get('modules') or []):
            pm=part.get(mod)
            files={};paths=[]
            if pm:
                for c in pm.get('candidates',[]):paths+=c['paths']
            for p in list(paths):
                d=str(Path(p).parent)
                for q in ls(d):
                    if q.endswith('.lean') and ('External' in q or 'Types' in q or q==p):paths.append(q)
            for p in dict.fromkeys(paths):files[p]=git_show(p)
            for name,fx in sorted(ext.items()):
                hits=search_gate(files,name)
                res['entries'].append(dict(spec=sid,run=run,gate_module=mod,external_name=name,fresh_form=fx,gate_hits=hits,
                  gate_form=(sorted({h['form'] for h in hits}) or ['NOT_FOUND']),hand_model=any(h['form'] not in('axiom','opaque','theorem') for h in hits),
                  origin=('selection opacity: this job passed --opaque for it (the gate defines the body); not a gate hand-written model of an external' if name in opq else 'Aeneas external of std/dependency crate or std-model'),pinned_crate=pinned(name),searched_files=sorted(files)))
(E/'PCQC_HAND_MODELS.json').write_text(json.dumps(res,indent=1)+'\n')
print(len(res['entries']),'entries;',sum(1 for x in res['entries'] if x['hand_model']),'hand models;',sum(1 for x in res['entries'] if x['gate_form']==['NOT_FOUND']),'not found')
