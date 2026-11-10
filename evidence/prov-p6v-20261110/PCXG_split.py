import sys,json,re
# PCXG_split.py <bundle> <name:firstsection-lastsection>... : splits a bundle at section boundaries; every part keeps the full hoisted import header and file texts unchanged.
b=sys.argv[1];L=open(b+'.lean').read().split('\n')
first=next(i for i,l in enumerate(L) if l.startswith('section PRVBundle_0'))
head=L[:first]
idx={}
for i,l in enumerate(L):
    m=re.match(r'section PRVBundle_(\d+)$',l)
    if m: idx[int(m.group(1))]=i
ends={}
for i,l in enumerate(L):
    m=re.match(r'end PRVBundle_(\d+)$',l)
    if m: ends[int(m.group(1))]=i
parts={}
for a in sys.argv[2:]:
    n,r=a.split(':');lo,hi=map(int,r.split('-'))
    txt=head[:]
    txt[0]=txt[0]+' -- PCXG split part %s: sections %d..%d of %s, texts unchanged'%(n,lo,hi,b)
    txt+=L[idx[lo]:ends[hi]+1]+['']
    open(n+'.lean','w').write('\n'.join(txt))
    parts[n]=[lo,hi]
json.dump(parts,open('PCXG_SPLIT_'+b+'.json','w'))
print(parts)
