#!/usr/bin/env python3
"""PCQF_HAND_MODELS.json (standing addendum): for each good PCQF run, every external (axiom/opaque) name of its emission, with the
gate's definition of that name in the gate modules the run is meant to cover (P2b gate_sources.json, P2c PCUC_EQ_STATUS gate_path).
RECORD ONLY: no trust row is added or proposed. hand_model = the gate defines the name concretely (def/abbrev/instance/structure/inductive)
where the fresh emission keeps it external. NOT_FOUND = no gate declaration of that name in the searched files."""
import json,re,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent;ZK=str(EV.parent)
def J(p):return json.loads(Path(p).read_text())
LOCK=subprocess.run(['git','-C',ZK,'show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],capture_output=True,text=True).stdout
def pinned(name):
    first=name.split('.')[0]
    if first in('core','alloc','std'):return 'Rust %s library, rustc nightly-2026-09-17 sysroot (tool pin PCQF_*_PINS.json; no crate version)'%first
    for c in (first.replace('_','-'),first):
        m=re.search(r'\[\[package\]\]\nname = "%s"\nversion = "([^"]+)"'%re.escape(c),LOCK)
        if m:return '%s %s (Cargo.lock 4bb3b3f5)'%(c,m.group(1))
    return 'workspace/unknown: '+first
def gshow(path):
    r=subprocess.run(['git','-C',ZK,'show','HEAD:'+path],capture_output=True,text=True);return r.stdout if r.returncode==0 else None
gate={}
for m,v in J(EV/'prov-p2b-20261109/inputs/gate_sources.json').items():gate[m]=v['paths'][:1]
for m,x in J(EV/'prov-p2c-20261109/PCUC_EQ_STATUS.json')['modules'].items():
    if x['passes']:gate[m]=[x['passes'][0]['gate_path']]
FRESH=re.compile(r"^((?:@\[[^\n]*\]\n)?)(axiom|opaque)\s+([^\s:(\[{]+)(.*?)(?=\n\n|\n/--|\Z)",re.M|re.S)
GATE=re.compile(r"^(?:@\[[^\n]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(def|abbrev|instance|axiom|opaque|structure|inductive|theorem)\s+(\S+)",re.M)
res=dict(schema=1,target_established=False,note='Record only; no trust row added or proposed. Name match: exact or suffix after the gate namespace.',entries=[],unlocated_gate_modules=[])
cache={}
def gate_text(mod):
    out={}
    for p in gate.get(mod,[]):
        if p not in cache:cache[p]=gshow(p)
        out[p]=cache[p]
    return out
for f in sorted(E.glob('PCQF_E[0-9][0-9][0-9]_spec.json')):
    s=J(f);run=s['run'];rc=E/run/'receipt.json'
    if not rc.exists() or J(rc)['exit_status']!=0:continue
    ext={}
    for lf in sorted((E/(run+'_emitted/raw')).glob('*/*.lean')):
        for pre,kind,name,rest in FRESH.findall(lf.read_text()):ext[name]=dict(file=str(lf.relative_to(EV)),text=(pre+kind+' '+name+rest).strip()[:600])
    opq={o.replace('crate::','').replace('::','.') for o in s['configuration'].get('opaque',[])}
    for mod in (s.get('covers') or {}).get('modules',[]):
        files=gate_text(mod)
        if not files:res['unlocated_gate_modules'].append(dict(run=run,module=mod));continue
        for name,fx in sorted(ext.items()):
            hits=[]
            for path,txt in files.items():
                if txt is None:continue
                lines=txt.split('\n')
                for m in GATE.finditer(txt):
                    n=m.group(2)
                    if n==name or n.endswith('.'+name) or name.endswith('.'+n):
                        ln=txt[:m.start()].count('\n');end=ln
                        while end<len(lines) and (end==ln or lines[end].strip()!=''):end+=1
                        hits.append(dict(file=path,line=ln+1,gate_name=n,form=m.group(1),text='\n'.join(lines[ln:min(end,ln+30)])))
            res['entries'].append(dict(run=run,spec=s['spec_id'],gate_module=mod,external_name=name,fresh_form=fx,gate_hits=hits,gate_form=sorted({h['form'] for h in hits}) or ['NOT_FOUND'],
              hand_model=any(h['form'] not in('axiom','opaque','theorem') for h in hits),
              origin='selection opacity (--opaque passed by this job)' if name in opq else 'Aeneas external of std/dependency crate or std-model',pinned_crate=pinned(name)))
(E/'PCQF_HAND_MODELS.json').write_text(json.dumps(res,indent=1)+'\n')
print(len(res['entries']),'entries;',sum(x['hand_model'] for x in res['entries']),'hand models;',sum(x['gate_form']==['NOT_FOUND'] for x in res['entries']),'not found;',len(res['unlocated_gate_modules']),'modules without gate path')
