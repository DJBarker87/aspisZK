import json,sys
sys.path.insert(0,'.')
import PCUF_gen_equalities as G
from pathlib import Path
import difflib
plan=json.load(open('PCUF_PLAN.json'))
def show(m,idx,fn,w=1500):
    ps=plan[m]['passes'][idx]
    k='Types.lean' if ps['kind']=='Types' else 'Funs.lean'
    fb={b['name']:b for b in G.parse_blocks((Path('..')/ps['fresh_dir']/k).read_text()) if b['kind']=='decl'}
    gb={b['name']:b for b in G.parse_blocks(Path('..',ps['gate']).read_text()) if b['kind']=='decl'}
    gn=ps['name_map'].get(fn,fn)
    a=G.norm_decl(fb[fn]).split();b=G.norm_decl(gb[gn]).split()
    print('##',m,idx,fn,'->',gn,ps['run'])
    print(' '.join(difflib.unified_diff(a,b,'fresh','gate',n=3,lineterm=''))[:w])
if __name__=='__main__':
    for spec in sys.argv[1:]:
        m,i,f=spec.split('|');show(m,int(i),f)
