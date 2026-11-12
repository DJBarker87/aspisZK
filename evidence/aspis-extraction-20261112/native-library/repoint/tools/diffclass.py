"""Compare every chain module with its text at <base_rev>; classify each removed/added line.
Classes: import (an `import` line), raw-open (an `open` line whose only change is BinHonestQueryBudget ->
AspisHonestBudgetBase), moved (a removed line of AspisRowStarts that occurs, in order, in AspisRowStarts33),
other (anything else: must not occur). Usage: diffclass.py <repo> <base_rev> <lean_dir_rel> <module_list>"""
import sys,subprocess,difflib,hashlib,os
repo,rev,rel,lst=sys.argv[1:5]
mods=[l.strip() for l in open(lst) if l.strip()]
def old(m):
    r=subprocess.run(['git','-C',repo,'show',f'{rev}:{rel}/{m}.lean'],capture_output=True)
    return r.stdout.decode().split('\n') if r.returncode==0 else None
new33=open(f'{repo}/{rel}/AspisRowStarts33.lean').read().split('\n')
print('module\tlines_removed\tlines_added\tkinds\tother_lines\tsha256_after')
bad=0
for m in mods:
    a=old(m); bt=open(f'{repo}/{rel}/{m}.lean','rb').read(); b=bt.decode().split('\n')
    sha=hashlib.sha256(bt).hexdigest()
    if a is None: print(f'{m}\tNEW\t{len(b)}\tnew module\t-\t{sha}'); continue
    rem=[];add=[]
    for op,i1,i2,j1,j2 in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes():
        if op!='equal': rem+=a[i1:i2]; add+=b[j1:j2]
    kinds=set(); other=[]
    radd=list(add)
    for l in rem:
        if l.startswith('import '): kinds.add('import'); continue
        if l.startswith('open ') and 'BinHonestQueryBudget' in l and l.replace('BinHonestQueryBudget','AspisHonestBudgetBase') in radd:
            radd.remove(l.replace('BinHonestQueryBudget','AspisHonestBudgetBase')); kinds.add('raw-open'); continue
        if m=='AspisRowStarts' and l in new33: kinds.add('moved to AspisRowStarts33'); continue
        other.append('-'+l)
    for l in radd:
        if l.startswith('import '): kinds.add('import'); continue
        if l.startswith('open ') and 'AspisHonestBudgetBase' in l: continue
        other.append('+'+l)
    if other: bad+=1
    if rem or add:
        print(f'{m}\t{len(rem)}\t{len(add)}\t{",".join(sorted(kinds))}\t{" | ".join(other) if other else "-"}\t{sha}')
    else:
        print(f'{m}\t0\t0\tunchanged\t-\t{sha}')
print(f'# modules with other changes: {bad}',file=sys.stderr)
