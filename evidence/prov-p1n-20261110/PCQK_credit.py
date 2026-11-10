#!/usr/bin/env python3
"""PCQK_credit.py SCOPE... : per exit-0 scope list proved theorems (declared in the scope's file, axioms standard only) and the commented obligations."""
import json,re,sys,glob
STD={'propext','Classical.choice','Quot.sound'}
out={}
for a in sys.argv[1:]:
    r=json.load(open(f'PCQK_{a}/receipt.json'));assert r['exit_status']==0
    src=open(r['sources'][0].replace('PCQK_sources/','')).read() if False else open(r['sources'][0].split('/')[-1]).read()
    assert 'sorry' not in src and 'native_decide' not in src
    th=[];
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x);m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",x)
        ax={s.strip() for s in (m.group(2) or '').split(',') if s.strip()}
        th.append(dict(theorem=m.group(1),axioms_standard_only=ax<=STD,axioms=sorted(ax)))
    obl=[re.sub(r'\s+',' ',l)[:230] for l in re.findall(r'(?m)^/- PRV-OBLIGATION[^\n]*',src)]
    out[a]=dict(module=r['module'],exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],theorems=th,obligations=obl)
    print(a,r['module'],len(th),'proved',all(t['axioms_standard_only'] for t in th),len(obl),'obligations')
json.dump(out,open(sys.argv[0].replace('.py','')+'_out.json','w'),indent=1)
