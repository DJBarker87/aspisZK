#!/usr/bin/env python3
"""PCT_handmodels.py: for every verified pass, each external/leaked name that the generator resolves to a gate definition; record gate def text, kind, fresh form, crate, dependents. Records only (no trust rows)."""
import json,re,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True;sys.path.insert(0,'.')
import PCT_gen_equalities as G
def show(p):
    r=subprocess.run(['git','show',f'research:{p}'],capture_output=True);return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
CRATE={'solana_pubkey':('solana-pubkey','2.4.0'),'solana_hash':('solana-hash','2.3.0')}
prep=json.load(open('gen/prepared2.json'));P=json.load(open('PCT_PARTITION.json'))['modules'];st=json.load(open('PCT_STATUS.json'))['modules']
out=[]
for m,r in prep.items():
    for ps in r['passes']:
        label=m.replace('.','_')+ps['tag'];rep=json.load(open(f'gen/PRVEq_{label}.report2.json'))
        names=sorted(set(rep['external_types'])|set(rep['external_funs'])|set(rep['names_resolved_to_gate_funs']))
        if not names: continue
        gtext=Path('inputs/gate_'+label+'.lean').read_text()
        gp=ps['gate_path'];ext=[]
        for a,b in (('Funs.lean','FunsExternal.lean'),('Types.lean','TypesExternal.lean'),('Funs.lean','Types.lean')):
            if gp.endswith(a):
                t=show(gp[:-len(a)]+b)
                if t: ext.append((gp[:-len(a)]+b,t))
        files=[(gp,gtext)]+ext
        import os
        d0=os.path.dirname(gp)
        for dd in (d0,os.path.dirname(d0)):
            lst=subprocess.run(['git','ls-tree','-r','--name-only','research',dd+'/'],capture_output=True,text=True).stdout.split()
            for q in lst:
                if q.endswith('.lean') and q!=gp and len(files)<40 and q not in [x[0] for x in files]:
                    t=show(q)
                    if t: files.append((q,t))
        fresh=Path('inputs/fresh_'+label)
        fblocks=[]
        for fn in ('Funs.lean','Types.lean'):
            if (fresh/fn).exists(): fblocks+=[b for b in G.parse_blocks((fresh/fn).read_text()) if b['kind']=='decl']
        extern_fresh=set(rep['external_types'])|set(rep['external_funs'])
        reached=set(k.split('.',1)[1] if False else k for k in st[m]['reached'])
        gns=rep['gate_namespace']
        for n in names:
            found=None
            for path,t in files:
                for b in G.parse_blocks(t):
                    if b['kind']=='decl' and b['name'] in (n,gns+'.'+n): found=(path,b);break
                if found: break
            deps=sorted({gns+'.'+fb['name'] for fb in fblocks if re.search(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])',fb['body']) and gns+'.'+fb['name'] in st[m]['reached']})
            crate=next((v for k,v in CRATE.items() if n.startswith(k+'.')),None) or (('rust std/core/alloc (toolchain pinned in the frozen rust-toolchain; not a Cargo.lock crate)',None) if n.split('.')[0] in('core','alloc','Slice','Array') else None)
            if found:
                path,b=found;kind=b['dkind'];aeneas_src='Source:' in b['text'] and '[' in b['text'].split('Source:')[0][-300:]
                cls='aeneas_external_axiom_or_opaque' if kind in('axiom','opaque') else ('extracted_from_frozen_source' if aeneas_src else 'hand_written_model')
                gd=dict(file=path,kind=kind,text=b['text'])
            else: cls='definition_not_in_gate_source_files_examined (imported module)';gd=dict(note='declaration not found in the gate source candidate, its sibling external files, or other .lean files in its directory and parent; defined in an imported gate module whose text was not examined',gate_source_imports=re.findall(r'(?m)^import\s+(\S+)',gtext))
            out.append(dict(gate_module=m,pass_tag=ps['tag'],external_name=n,fresh_form='axiom (external template)' if n in extern_fresh else 'name used by fresh text, not declared in the fresh emission' ,gate_definition=gd,classification=cls,models_crate_and_version=crate,reached_definitions_depending=deps))
Path('PCT_HAND_MODELS.json').write_text(json.dumps(dict(note='Recording only; no trust rows are added or proposed. classification hand_written_model = gate declaration without an Aeneas Source docstring.',entries=out),indent=1))
import collections;print(len(out),collections.Counter(e['classification'] for e in out))
