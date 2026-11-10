import sys,re,lzma,json
L,mod=sys.argv[1:3]
src=open(f'PRVEq_{mod}_P3.lean').read().split('\n')
log=lzma.open(f'{L}/stdout.log.xz','rt').read()
thm=[(i+1,re.match(r'theorem (\S+)',l).group(1)) for i,l in enumerate(src) if l.startswith('theorem PRVC.Eq.') or l.startswith('theorem PRVEq.')]
def owner(line):
    o=None
    for ln,n in thm:
        if ln<=line: o=n
    return o
seen={}
for m in re.finditer(r'PCVD_sources/\S+?\.lean:(\d+):(\d+): error[^\n]*\n([^\n]*)',log):
    ln=int(m.group(1)); o=owner(ln)
    seen.setdefault(o,[]).append((ln,m.group(0).split('error')[1][:90].replace('\n',' '),m.group(3)[:100]))
ok=re.findall(r"'(PRVC\.Eq\.\S+)' depends on axioms: \[(propext, Classical.choice, Quot.sound|propext, Classical.choice, Quot.sound)\]",log)
okl=re.findall(r"'(PRVC\.Eq\.\S+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
good=[n for n,a in okl if 'sorryAx' not in a]
print('PROVED',len(good),'ERRORS in',len(seen))
for o,v in seen.items(): print(' ',o,v[0])
