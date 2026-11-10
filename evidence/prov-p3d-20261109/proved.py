import sys,re,lzma,json
def proved(L):
    log=lzma.open(f'{L}/stdout.log.xz','rt').read()
    out={}
    for m in re.finditer(r"'(PRV\S+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log):
        ax=[a.strip() for a in (m.group(2) or '').replace('\n',' ').split(',') if a.strip()]
        out[m.group(1)]=ax
    err=len(re.findall(r'error',log))
    return out,err
if __name__=='__main__':
    for L in sys.argv[1:]:
        o,e=proved(L)
        bad=[k for k,v in o.items() if not set(v)<= {'propext','Classical.choice','Quot.sound'}]
        print(L,'errors-lines',e,'theorems',len(o),'nonstandard',bad)
        for k in o:
            if k.startswith('PRVC.Eq.'): print('  ',k)
