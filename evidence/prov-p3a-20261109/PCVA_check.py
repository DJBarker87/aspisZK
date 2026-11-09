#!/usr/bin/env python3
"""PCVA_check.py ATTEMPT SRC.lean : exit-0 verification summary: theorem count, #print axioms lines (standard only), forbidden tokens."""
import sys,json,re
a,src=sys.argv[1:3]
r=json.load(open(a+'/receipt.json'));t=open(src).read()
ax=r['print_axioms'];bad=[x for x in ax if 'depends on axioms' in x and not set(re.findall(r'\[(.*)\]',x.replace('\n',' '),re.S)[0].replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}]
code='\n'.join(l for l in t.split('\n') if not l.lstrip().startswith('--'))
toks={k:len(re.findall(k,code)) for k in ['sorry','native_decide','axiom ','decide','norm_num','maxHeartbeats']}
nth=len(re.findall(r'^theorem ',t,re.M))
print(json.dumps(dict(attempt=a,exit=r['exit_status'],theorems=nth,axiom_lines=len(ax),nonstandard=bad,tokens=toks,wall=r['wall_seconds'],rss_kib=r['peak_rss_kib'],swaps=r['swaps'])))
