#!/usr/bin/env python3
"""Carrier-free copy of L187 modules: remove only `import X` lines where X is in the d-set.
Every other byte is identical. Records a per-module diff line in TRIM_RECORD.tsv.
Usage: trim_imports.py <src_dir> <out_dir> <d_list_file> <module>..."""
import sys,os,hashlib
src,out,dfile=sys.argv[1:4]; mods=sys.argv[4:]
d=set(l.split('\t')[0].strip() for l in open(dfile) if l.strip() and not l.startswith('d_module'))
rec=open(os.path.join(out,'TRIM_RECORD.tsv'),'a')
for m in mods:
    p=os.path.join(src,m.replace('.','/')+'.lean'); txt=open(p,'rb').read()
    lines=txt.split(b'\n'); kept=[]; removed=[]
    for l in lines:
        s=l.decode('utf-8','replace').strip()
        if s.startswith('import ') and s[7:].strip() in d: removed.append(s[7:].strip())
        else: kept.append(l)
    new=b'\n'.join(kept)
    q=os.path.join(out,m.replace('.','/')+'.lean'); os.makedirs(os.path.dirname(q),exist_ok=True); open(q,'wb').write(new)
    rec.write(f"{m}\t{hashlib.sha256(txt).hexdigest()}\t{hashlib.sha256(new).hexdigest()}\t{','.join(removed) or '-'}\n")
    print(m,'removed:',removed or 'none')
