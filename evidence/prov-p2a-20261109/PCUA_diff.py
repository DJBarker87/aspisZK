#!/usr/bin/env python3
"""PCUA_diff.py JOB ...: normalized-text diffs (comments/whitespace/registration attributes dropped) between each failed or
non-identical common definition of the fresh emission and the gate source, as used for FAILED entries of PCUA_EQ_STATUS.json."""
import sys,json,difflib,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
import PCUA_gen_equalities as G
import PCUA_jobs as J
def blocks(p):return {b['name']:b for b in G.parse_blocks(Path(p).read_text()) if b['kind']=='decl'}
def toks(s):return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+#?\w*|[^\sA-Za-z0-9_]",s)
def diff_job(jid):
    j=J.JOBS[jid];kind=j.get('kind') or ('types' if j['M'].endswith('Types') else 'funs')
    fb=blocks(Path(j['fresh'])/('Types.lean' if kind=='types' else 'Funs.lean'));gb=blocks(H/'gate_src'/j['gate'])
    out={}
    for n,b in fb.items():
        if n in gb:
            a=G.norm_decl(b);c=G.norm_decl(gb[n])
            if a==c:continue
            ta,tc=toks(a),toks(c)
            d=[l for l in difflib.unified_diff(tc,ta,'gate','fresh',n=2,lineterm='') if not l.startswith(('---','+++'))]
            out[n]=dict(identical=False,diff_gate_to_fresh=' '.join(d)[:4000])
    return out
if __name__=='__main__':
    res={jid:diff_job(jid) for jid in sys.argv[1:]}
    print(json.dumps(res,indent=1))
