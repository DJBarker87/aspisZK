import pathlib,re,json,difflib,sys
raw=pathlib.Path('../prov-p1e-20261109/PCQF_E005_emitted/raw/PCQF_aspis_statement_pool_v1_pair_terminal/Funs.lean').read_text().split('\n')
gate=pathlib.Path('../prov-p2j-20261110/inputs/gate_AspisR1TerminalDecoder_Funs.lean').read_text().split('\n')
def grab(L,start_pat):
    s=next(i for i,l in enumerate(L) if l==start_pat or l.startswith(start_pat+' '))
    e=next(i for i in range(s+1,len(L)) if L[i].startswith('/--') or L[i].startswith('end ') or L[i].startswith('#print') or L[i].startswith('@['))
    return '\n'.join(L[s:e])
n='def pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1'
a=grab(raw,n);b=grab(gate,n)
tok=lambda s:re.findall(r"[\w.'«»#]+|[^\s\w]",s)
ta=[t.replace('_root_.','') for t in tok(a)];tb=[t.replace('_root_.','') for t in tok(b)]
sm=difflib.SequenceMatcher(None,ta,tb,autojunk=False)
ops=[o for o in sm.get_opcodes() if o[0]!='equal']
r=dict(note='TEXTUAL token-stream comparison, whitespace-insensitive; NOT a Lean-checked equality and earns no credit',raw_tokens=len(ta),gate_tokens=len(tb),equal=ta==tb,n_diff_ops=len(ops),first=[[o[0],ta[o[1]:o[2]][:8],tb[o[3]:o[4]][:8]] for o in ops[:12]])
json.dump(r,open('PCVI_decode_token_check.json','w'),indent=1);print(json.dumps(r)[:1500])
