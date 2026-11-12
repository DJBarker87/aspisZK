#!/usr/bin/env python3
"""Carrier-free copy of L187 modules. For each `import X` line with X a carrier (kind-d):
replace it by the base module(s) mapped for X, or delete it when X has no mapping.
Every other byte is identical. Records module, sha before, sha after, replaced/removed imports.
Usage: trim_imports.py <src_dir> <out_dir> <kind-d.tsv> [--map carrier=Base1,Base2 ...] <module>..."""
import sys,os,hashlib
args=sys.argv[1:]; src,out,dfile=args[:3]; rest=args[3:]
imap={}; mods=[]
i=0
while i<len(rest):
    if rest[i]=='--map': k,v=rest[i+1].split('='); imap[k]=v.split(','); i+=2
    else: mods.append(rest[i]); i+=1
d=set(l.split('\t')[0].strip() for l in open(dfile) if l.strip() and not l.startswith('d_module'))
os.makedirs(out,exist_ok=True); rec=open(os.path.join(out,'TRIM_RECORD.tsv'),'a')
for m in mods:
    p=os.path.join(src,m.replace('.','/')+'.lean'); txt=open(p,'rb').read()
    kept=[]; changed=[]
    for l in txt.split(b'\n'):
        s=l.decode('utf-8','replace').strip()
        if s.startswith('import ') and s[7:].strip() in d:
            c=s[7:].strip()
            if c in imap:
                for b in imap[c]: kept.append(('import '+b).encode())
                changed.append(f"{c}->{'+'.join(imap[c])}")
            else: changed.append(f"{c}->(removed)")
        else: kept.append(l)
    new=b'\n'.join(kept)
    q=os.path.join(out,m.replace('.','/')+'.lean'); os.makedirs(os.path.dirname(q),exist_ok=True); open(q,'wb').write(new)
    rec.write(f"{m}\t{hashlib.sha256(txt).hexdigest()}\t{hashlib.sha256(new).hexdigest()}\t{';'.join(changed) or '-'}\n")
    print(m,'imports changed:',changed or 'none')
