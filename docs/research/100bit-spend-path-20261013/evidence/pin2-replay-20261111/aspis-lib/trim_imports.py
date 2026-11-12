#!/usr/bin/env python3
"""Carrier-free copy of L187 modules (revision 4).
For each `import X` line: if X is a mapped carrier, the line becomes `import <Base>` for each mapped base;
if X is an unmapped carrier or an omitted module, the line is replaced by X's carrier-free import frontier
(X's imports, with carriers/omitted modules expanded recursively the same way: mapped ones -> their bases,
others -> their own imports), so nothing an import brought in transitively is lost. Every other byte identical.
Records module, sha before, sha after, and each replacement.
Usage: trim_imports.py <src_dir> <out_dir> <kind-d.tsv> [--omit OMIT_MODULES.txt] [--map carrier=Base1,Base2 ...] <module>..."""
import sys,os,hashlib
args=sys.argv[1:]; src,out,dfile=args[:3]; rest=args[3:]
imap={}; mods=[]; omit=set(); i=0
while i<len(rest):
    if rest[i]=='--map': k,v=rest[i+1].split('='); imap[k]=v.split(','); i+=2
    elif rest[i]=='--omit': omit|=set(l.strip() for l in open(rest[i+1]) if l.strip()); i+=2
    else: mods.append(rest[i]); i+=1
d=set(l.split('\t')[0].strip() for l in open(dfile) if l.strip() and not l.startswith('d_module'))
expand=d|omit
def imports(m):
    p=os.path.join(src,m.replace('.','/')+'.lean')
    return [l.split()[1] for l in open(p,errors='ignore') if l.startswith('import ')] if os.path.exists(p) else []
def frontier(x,seen):
    """replacement import list for a single import x"""
    if x in imap: return list(imap[x])
    if x not in expand: return [x]
    out=[]
    for y in imports(x):
        if y in seen: continue
        seen.add(y); out.extend(frontier(y,seen))
    return out
os.makedirs(out,exist_ok=True); rec=open(os.path.join(out,'TRIM_RECORD.tsv'),'a')
for m in mods:
    p=os.path.join(src,m.replace('.','/')+'.lean'); txt=open(p,'rb').read()
    kept=[]; changed=[]; have=set()
    for l in txt.split(b'\n'):
        s=l.decode('utf-8','replace').strip()
        if s.startswith('import '):
            x=s[7:].strip()
            if x in expand:
                repl=[r for r in dict.fromkeys(frontier(x,set([x]))) if r not in have]
                for r in repl: kept.append(('import '+r).encode()); have.add(r)
                changed.append(f"{x}->{'+'.join(repl) or '(nothing)'}")
            else:
                if x not in have: kept.append(l); have.add(x)
        else: kept.append(l)
    new=b'\n'.join(kept)
    q=os.path.join(out,m.replace('.','/')+'.lean'); os.makedirs(os.path.dirname(q),exist_ok=True); open(q,'wb').write(new)
    rec.write(f"{m}\t{hashlib.sha256(txt).hexdigest()}\t{hashlib.sha256(new).hexdigest()}\t{';'.join(changed) or '-'}\n")
    print(m,'imports changed:',len(changed))
