import sys,collections
g_file,dfile,chainfile=sys.argv[1:4]
D=set(l.strip() for l in open(dfile) if l.strip())
chain=set(l.strip() for l in open(chainfile) if l.strip())
lib={'AspisLib_SourceInputs','AspisLib_Recorded','AspisLib_Tag','AspisLib_QueryAccounting','AspisLib_Guard','AspisHonestBudgetBase'}
imp=collections.defaultdict(list); mods=set()
for l in open(g_file):
    a,_,b=l.rstrip('\n').partition('\t'); mods.add(a)
    if b: imp[a].append(b)
# closure from root
root='AspisFailureBoundModel'; seen=set(); st=[root]
while st:
    x=st.pop()
    if x in seen: continue
    seen.add(x); st.extend(imp[x])
def kind(m): return 'a' if m in chain else ('lib' if m in lib else ('d' if m in D else 'c/other'))
dins=sorted(m for m in seen if m in D)
print('# closure modules',len(seen),'kind d in closure',len(dins))
print('d_module\timported_by_in_closure(kind)')
for m in dins:
    by=sorted(a for a in seen if m in imp[a])
    print(m+'\t'+', '.join(f'{a}({kind(a)})' for a in by))
print('# entry edges: non-d module in closure -> d module')
for a in sorted(seen):
    if a in D: continue
    for b in imp[a]:
        if b in D: print(f'{a}({kind(a)}) -> {b}')
for a in sorted(seen):
    if a in chain:
        for b in imp[a]:
            if b in D: print('CHAIN-DIRECT-D',a,b)
for t in ['AspisRowStarts33','AspisChargedWeight','AspisChargedHitMass','AspisChargedHitMassCheck','BinHonestQueryBudget']:
    print('in_closure',t,t in seen)
print('# per d module: entry edges (c -> d0) from which it is reached through d-only imports')
print('d_module\tentry_edges')
entries=[(a,b) for a in seen if a not in D for b in imp[a] if b in D]
def dreach(x):
    r=set();st=[x]
    while st:
        y=st.pop()
        if y in r: continue
        r.add(y); st.extend(z for z in imp[y] if z in D)
    return r
reach={b:dreach(b) for _,b in entries}
for m in dins:
    es=sorted(f'{a} -> {b}' for a,b in entries if m in reach[b])
    print(m+'\t'+'; '.join(es))
