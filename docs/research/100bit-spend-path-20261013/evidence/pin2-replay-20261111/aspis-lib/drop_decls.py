#!/usr/bin/env python3
"""Delete named top-level declarations from (already trimmed or original) module copies.
A declaration spans from its header line (def/theorem/abbrev/lemma/structure/instance/...) back over any
directly preceding doc comment (/-- ... -/) and attribute lines (@[...]), forward to the line before the next
top-level token at column 0. Every other byte is identical. Records module, decl, sha256 of the removed text.
Usage: drop_decls.py <src_dir> <out_dir> <DROP_DECLS.tsv>   (rows: module<TAB>short_decl_name)"""
import sys,os,re,hashlib,collections
src,out,tsv=sys.argv[1:4]
drops=collections.defaultdict(list)
for l in open(tsv):
    if l.strip(): m,n=l.rstrip('\n').split('\t'); drops[m].append(n)
rec=open(os.path.join(out,'DROP_RECORD.tsv'),'a')
HEAD=re.compile(r'^(?:noncomputable\s+|private\s+|protected\s+)*(def|theorem|lemma|abbrev|structure|inductive|instance|opaque|axiom)\s+([^\s(:{]+)')
TOP=re.compile(r'^(?:noncomputable\s+|private\s+|protected\s+)*(def|theorem|lemma|abbrev|structure|inductive|instance|opaque|axiom|example|namespace|end|section|open|variable|set_option|/--|/-|@\[|#)')
for m,names in drops.items():
    p=os.path.join(out,m.replace('.','/')+'.lean')
    if not os.path.exists(p): p=os.path.join(src,m.replace('.','/')+'.lean')
    lines=open(p,'rb').read().split(b'\n'); text=[l.decode('utf-8','replace') for l in lines]
    keep=[True]*len(lines)
    for n in names:
        hits=[i for i,l in enumerate(text) if (h:=HEAD.match(l)) and h.group(2).split('.')[-1]==n.split('.')[-1] and (h.group(2)==n or h.group(2).endswith('.'+n) or n.endswith('.'+h.group(2)) or h.group(2)==n.split('.')[-1])]
        if len(hits)!=1: print(f"!! {m}.{n}: {len(hits)} header matches, skipped"); continue
        s=hits[0]; e=s+1
        while e<len(text) and not TOP.match(text[e]): e+=1
        while e>s+1 and text[e-1].strip()=='' : e-=1
        b=s
        while b>0 and (text[b-1].startswith('@[') or text[b-1].rstrip().endswith('-/') or (text[b-1].strip()=='' and False)): 
            # include an immediately preceding doc comment block
            if text[b-1].rstrip().endswith('-/'):
                j=b-1
                while j>=0 and not text[j].lstrip().startswith('/--') and not text[j].lstrip().startswith('/-'): j-=1
                if j<0: break
                b=j
            else: b-=1
        removed=b'\n'.join(lines[b:e])
        for i in range(b,e): keep[i]=False
        rec.write(f"{m}\t{n}\t{b+1}-{e}\t{hashlib.sha256(removed).hexdigest()}\n"); print(f"{m}: dropped {n} lines {b+1}-{e}")
    q=os.path.join(out,m.replace('.','/')+'.lean'); os.makedirs(os.path.dirname(q),exist_ok=True)
    open(q,'wb').write(b'\n'.join(l for l,k in zip(lines,keep) if k))
