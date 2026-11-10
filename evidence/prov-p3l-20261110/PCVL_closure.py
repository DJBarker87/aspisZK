import sys,re,json
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import importlib.util
spec=importlib.util.spec_from_file_location('g','PCVL_gen_equalities.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
txt=open('inputs/fresh_top/Funs.lean').read()
ext=g.parse_externals(open('inputs/fresh_top/FunsExternal_Template.lean').read())
blocks=[b for b in g.parse_blocks(txt) if b['kind']=='decl']
names={b['name']:b for b in blocks}
def toks(b): return set(g.lean_ident_tokens(b['body']))
roots=sys.argv[1:]
seen=[];stack=list(roots);used_ext=set();missing=set()
while stack:
    n=stack.pop()
    if n in seen: continue
    seen.append(n)
    b=names[n]
    t=toks(b)
    for m in names:
        if m!=n and m in t: stack.append(m)
    for e in ext:
        if e in t: used_ext.add(e)
print('defs',len(seen));print('ext',sorted(used_ext))
print([n for n in seen])
json.dump(dict(defs=seen,ext=sorted(used_ext)),open('gen/vtop_closure.json','w'),indent=1)
