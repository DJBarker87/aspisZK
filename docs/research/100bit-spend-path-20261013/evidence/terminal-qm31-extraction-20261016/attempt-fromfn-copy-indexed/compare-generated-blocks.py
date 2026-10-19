#!/usr/bin/env python3
"""Compare Aeneas generated Lean declaration bodies, without compiling them.

Usage: compare-generated-blocks-evidence.py OLD_GENERATED_DIR NEW_GENERATED_DIR OUTPUT_JSON
The directories each contain Funs.lean and Types.lean. Matching keys use the
Rust source file plus full Rust item name, deliberately ignoring shifted source
line spans. Exact Lean declaration bodies are SHA-256 compared after removing
the generated docblock. This is a textual audit only, not semantic equivalence.
"""
import collections, hashlib, json, re, sys
from pathlib import Path

def blocks(path):
    s = Path(path).read_text()
    starts = [m.start() for m in re.finditer(r'(?m)^/-- \[', s)]
    rows = []
    for i, start in enumerate(starts):
        end = starts[i+1] if i+1 < len(starts) else len(s)
        seg = s[start:end]
        head = re.search(r'^/-- \[(.*?)\]', seg, re.S)
        src = re.search(r"Source: '([^']+)', lines (\d+):(\d+)-(\d+):(\d+)", seg)
        if not head or not src:
            continue
        close = seg.find('-/')
        body = seg[close+2:].strip() if close >= 0 else ''
        key = (src.group(1), head.group(1))
        rows.append({'key':key,'source_span':{'start_line':int(src.group(2)),'start_col':int(src.group(3)),'end_line':int(src.group(4)),'end_col':int(src.group(5))},'body_sha256':hashlib.sha256(body.encode()).hexdigest()})
    return rows

def compare(old_rows,new_rows):
    old=collections.defaultdict(collections.Counter); new=collections.defaultdict(collections.Counter)
    spans_old=collections.defaultdict(list); spans_new=collections.defaultdict(list)
    for r in old_rows: old[r['key']][r['body_sha256']]+=1; spans_old[r['key']].append(r['source_span'])
    for r in new_rows: new[r['key']][r['body_sha256']]+=1; spans_new[r['key']].append(r['source_span'])
    exact=changed=old_only=new_only=0; changed_rows=[]; old_only_rows=[]; new_only_rows=[]
    for k in sorted(set(old)|set(new)):
        a,b=old[k],new[k]; shared=(a&b); nshared=sum(shared.values()); exact+=nshared
        rem_a=a-shared; rem_b=b-shared; na=sum(rem_a.values()); nb=sum(rem_b.values()); npair=min(na,nb); changed+=npair; old_only+=na-npair; new_only+=nb-npair
        if npair:
            changed_rows.append({'source':k[0],'rust_name':k[1],'old_body_sha256s':sorted(x for x,n in rem_a.items() for _ in range(n)),'new_body_sha256s':sorted(x for x,n in rem_b.items() for _ in range(n)),'old_spans':spans_old[k],'new_spans':spans_new[k]})
        if na>npair: old_only_rows.append({'source':k[0],'rust_name':k[1],'body_sha256s':sorted(x for x,n in rem_a.items() for _ in range(n))})
        if nb>npair: new_only_rows.append({'source':k[0],'rust_name':k[1],'body_sha256s':sorted(x for x,n in rem_b.items() for _ in range(n))})
    return {'old_blocks':len(old_rows),'new_blocks':len(new_rows),'exact_shared_bodies':exact,'changed_paired_bodies':changed,'old_only_declarations':old_only,'new_only_declarations':new_only,'changed':changed_rows,'old_only':old_only_rows,'new_only':new_only_rows}

def axioms(path):
    s=Path(path).read_text()
    return re.findall(r'(?m)^axiom\s+([^\s(:]+)',s)

def main():
    if len(sys.argv)!=4: raise SystemExit(__doc__)
    old,new,out=map(Path,sys.argv[1:])
    res={'scope':'generated Lean textual declaration-body comparison only; no Lean compile or semantic-equivalence conclusion','old_generated_dir':str(old),'new_generated_dir':str(new),'Funs':compare(blocks(old/'Funs.lean'),blocks(new/'Funs.lean')),'Types':compare(blocks(old/'Types.lean'),blocks(new/'Types.lean')),'FunsExternal_Template':{'old_axiom_count':len(axioms(old/'FunsExternal_Template.lean')),'new_axiom_count':len(axioms(new/'FunsExternal_Template.lean')),'old_axioms':axioms(old/'FunsExternal_Template.lean'),'new_axioms':axioms(new/'FunsExternal_Template.lean')},'input_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for d in (old,new) for p in sorted(d.glob('*.lean'))}}
    out.write_text(json.dumps(res,indent=2)+'\n')
    print(json.dumps({k:res[k] for k in ['scope','Funs','Types','FunsExternal_Template'] if k!='Funs'})[:3000])
if __name__=='__main__': main()
