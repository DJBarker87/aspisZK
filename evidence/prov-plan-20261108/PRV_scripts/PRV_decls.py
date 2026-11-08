import json,re,sys,collections
sys.path.insert(0,'emission-repro-20261110')
from NMH_names import uncomment
S=sys.argv[1]
rx=re.compile(r'(?m)^[ \t]*(?:(namespace)\s+(\S+)|(end)\b(?:[ \t]+(\S+))?|((?:noncomputable[ \t]+)?section)\b(?:[ \t]+\S+)?|(?:@\[[^\]\n]*\][ \t]*)*(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)[ \t]+)*(def|abbrev|structure|inductive|theorem|lemma|opaque|axiom|instance|class)\s+(?:\([^)]*\)\s*)?([^\s({:\[]+))')
def decls(s):
    clean=uncomment(s);scope=[];out=[]
    for m in rx.finditer(clean):
        if m[1]: 
            for part in [m[2]]: scope.append(('namespace',part))
        elif m[3]:
            if scope: scope.pop()
        elif m[5]: scope.append(('section',''))
        else:
            if m[6]=='instance' and m[7] in (':','where'): continue
            ns='.'.join(x[1] for x in scope if x[0]=='namespace')
            nm=m[7]
            if nm.startswith('_root_.'): full=nm[7:]
            else: full=(ns+'.' if ns else '')+nm
            out.append((full,m[6]))
    return out
modver=json.load(open(f"{S}/modver.json"))
res={}
for M,v in modver.items():
    for x in v['versions']:
        t=open(f"{S}/blobs/{x['blob']}.lean").read()
        x['decls']=decls(t)
json.dump(modver,open(f"{S}/modver_decls.json","w"))
print(sum(len(x['decls']) for v in modver.values() for x in v['versions']))
