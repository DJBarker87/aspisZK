#!/usr/bin/env python3
"""PCXK_gen.py: corrected copies of the 78 PCXJ-flagged PRVEq files (python3 -I -B; reads `git show research:<path>`).
Edit 1: the file/section-wide `set_option maxHeartbeats N` (N>200000) stays for the inlined Aeneas emission only; a line
`set_option maxHeartbeats 200000` is inserted immediately before the first theorem/lemma (before its attribute / doc comment / `set_option .. in` chain).
Edit 2: every `set_option maxHeartbeats N in` with N>200000 becomes 200000. Nothing else changes."""
import json, re, subprocess, hashlib, sys, os
REF='research'; here=os.path.dirname(os.path.abspath(__file__)); out=os.path.join(here,'PCXK_sources'); os.makedirs(out,exist_ok=True)
def show(p): return subprocess.run(['git','show',REF+':'+p],capture_output=True,check=True).stdout.decode()
hb=json.loads(subprocess.run(['git','show',REF+':evidence/prov-p6z-20261110/PCXJ_HEARTBEATS.json'],capture_output=True,check=True).stdout)
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s')
INOPT=re.compile(r'^(\s*set_option\s+maxHeartbeats\s+)(\d+)(\s+in\b.*)$')
WIDE=re.compile(r'^\s*set_option\s+maxHeartbeats\s+(\d+)\s*$')
res=[]
for p in sorted(hb['by_file']):
    src=show(p); L=src.split('\n'); n_in=0; wide=[]
    for i,l in enumerate(L):
        m=INOPT.match(l)
        if m and int(m.group(2))>200000: L[i]=m.group(1)+'200000'+m.group(3); n_in+=1
        w=WIDE.match(l)
        if w and int(w.group(1))>200000: wide.append((i+1,int(w.group(1))))
    first=next(i for i,l in enumerate(L) if DECL.match(l))
    j=first
    while j>0:
        pv=L[j-1].strip()
        if re.match(r'set_option\b.*\bin$',pv) or pv.startswith('@['): j-=1; continue
        if pv.endswith('-/'):
            k=j-1
            while k>=0 and not L[k].lstrip().startswith('/-'): k-=1
            if k>=0 and L[k].lstrip().startswith('/--'): j=k; continue
        break
    L.insert(j,'set_option maxHeartbeats 200000')
    # scope reset: an `end` that closes a namespace/section opened before the insertion restores the emission-wide value; re-assert 200000 after it.
    n_reasserted=0
    # second pass with explicit insertion (iterate to a fixed point on the end lines)
    out_lines=[]; wl=[200000]; kinds=[]
    for i,l in enumerate(L):
        out_lines.append(l); t=l.strip()
        if re.match(r'(namespace|section)\b',t): kinds.append(len(wl)); continue
        if re.match(r'end\b',t) and kinds:
            del wl[kinds.pop():]
            if i>j and wl[-1]>200000: out_lines.append('set_option maxHeartbeats 200000'); wl.append(200000); n_reasserted+=1
            continue
        w=WIDE.match(l)
        if w: wl.append(int(w.group(1)))
    L=out_lines
    # axioms audit: append `#print axioms Q` (Q = namespace-qualified name) at EOF for every theorem/lemma with no existing print of that qualified name
    stack=[]; thm=[]; printed=set(); DNAME=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+(\S+)')
    for l in L:
        t=l.strip(); m=re.match(r'namespace\s+(\S+)',t)
        if m: stack.append(('ns',m.group(1))); continue
        if re.match(r'section\b',t): stack.append(('sec','')); continue
        if re.match(r'end\b',t) and stack: stack.pop(); continue
        ns='.'.join(x[1] for x in stack if x[0]=='ns')
        d=DNAME.match(l)
        if d: thm.append((ns+'.'+d.group(1)) if ns else d.group(1))
        m=re.match(r'#print axioms\s+(\S+)',t)
        if m: printed.add(m.group(1)); printed.add((ns+'.'+m.group(1)) if ns else m.group(1))
    added=[q for q in thm if q not in printed]
    if added: L=L+['','-- PCXK: axioms audit lines appended for theorems that had no #print axioms in the original']+['#print axioms '+q for q in added]
    dst=src_name=p.replace('evidence/','').split('/')
    tag=dst[0].split('-')[1]; base=dst[-1]
    name='PCXK_%s__%s'%(tag,base)
    new='\n'.join(L)
    open(os.path.join(out,name),'w').write(new)
    res.append(dict(original=p,copy='PCXK_sources/'+name,original_sha256=hashlib.sha256(src.encode()).hexdigest(),copy_sha256=hashlib.sha256(new.encode()).hexdigest(),
        wide_options_kept_for_emission=[dict(line=a,value=b) for a,b in wide],inserted_line_200000_at=j+1,reasserted_after_end=n_reasserted,print_axioms_lines_appended=len(added),theorems=len(thm),first_theorem_line_in_copy=first+2,in_options_lowered_to_200000=n_in,
        diff_summary='%d line(s) inserted (set_option maxHeartbeats 200000 before first theorem/lemma, and after each `end` that restores the emission-wide option); %d `maxHeartbeats N in` (N>200000) lowered to 200000; %d `#print axioms` lines appended at EOF'%(1+n_reasserted,n_in,len(added)),theorems_above_200000_in_original=hb['by_file'][p]['above_200000']))
json.dump(dict(schema='PCXK_FILES/1',target_established=False,files=res),open(os.path.join(here,'PCXK_FILES.json'),'w'),indent=1)
print(len(res),sum(r['in_options_lowered_to_200000'] for r in res))
