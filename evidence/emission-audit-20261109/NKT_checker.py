#!/usr/bin/env python3
"""Conservative text audit, not an extractor/proof. Reads immutable Git objects.
Candidates require manual Rust/LLBC review; a hit alone is never an affected row.
"""
import argparse, collections, hashlib, json, lzma, pathlib, re, subprocess, time
OUT=pathlib.Path(__file__).resolve().parent
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def sha(b): return hashlib.sha256(b).hexdigest()
def sites(text):
    # Match individual none-valued done constructors, including multiline tuples.
    decls=list(re.finditer(r'(?m)^(?:(?:noncomputable|private|protected) )?(def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(]+)',text)); defs=[m for m in decls if m.group(1)=='def']
    result=[]
    for i,m in enumerate(defs):
        end=next((d.start() for d in decls if d.start()>m.start()),len(text))
        body=text[m.start():end]
        hits=[]
        for h in re.finditer(r'\bdone\s+',body):
            pos=h.end()
            if body.startswith('none',pos): value='none'
            elif pos<len(body) and body[pos]=='(':
                depth=0; stop=pos
                for stop in range(pos,len(body)):
                    if body[stop]=='(':depth+=1
                    elif body[stop]==')':
                        depth-=1
                        if depth==0:break
                value=body[pos:stop+1]
            else:continue
            if re.search(r'\bnone\b',value):
                hits.append({'line':text.count('\n',0,m.start()+h.start())+1,'text':'done '+value[:400]})
        caller=bool(re.search(r'match pending_return\w* with\s*\| none =>',body))
        if hits or caller:
            result.append({'definition':m.group(2),'line':text.count('\n',0,m.start())+1,'done_none':hits,'pending_return_caller':caller})
    return result
def run_controls(g):
    bp='evidence/batch-merkle-20261108/NJS_emitted/raw/NJS_Extract/Funs.lean'
    scanned=sites(g.text(bp));bt=next(d for d in scanned if d['definition']=='verifier.candidate.batch_tree_loop.body')
    lines={x['line'] for x in bt['done_none']}
    groups=[{'frozen_line':196,'exit':'node_count.ok_or(Merkle)?','lean_lines':[997]},
            {'frozen_line':200,'exit':'return Err(Parse), OR guard','lean_lines':[966,980]},
            {'frozen_line':203,'exit':'return Err(Merkle), verify false','lean_lines':[992]}]
    c={'batch_tree':{'path':bp,'syntactic_none_branches':len(lines),'rust_exit_groups':groups,'rust_exits':len(groups),'pass':lines=={966,980,992,997}}}
    for label,path,name in [('canonical_scan',bp,'verifier.candidate.canonical_scan_loop0.body'),('verify_in_place','evidence/multiproof-20261107/NJA_emitted/raw/NHR_NJA_multiproof/Funs.lean','multiproof.verify_in_place_loop0.body')]:
        t=g.text(path);m=re.search(r'(?m)^def '+re.escape(name)+r'\s',t);end=t.find('/--',m.end());body=t[m.start():end]
        tail=body.split('match o with',1)[1].split('| some ',1)[0]
        loss=sum(len(x['done_none']) for x in sites('def tail_control : Unit :=\n'+tail))
        c[label]={'path':path,'emission_sha256':sha(g.read(path)),'definition':name,'normal_exhaustion_branch':tail.strip(),'tail_loss_hits':loss,'pass':loss==0,
                  'raw_internal_warning_count':sum(len(x['done_none']) for x in sites(t) if label in x['definition'])}
    return c

class Git:
    def __init__(self,rev):
        self.rev=rev
        raw=subprocess.check_output(['git','ls-tree','-rz','--full-tree',rev])
        self.entries={}
        for e in raw.split(b'\0'):
            if not e: continue
            meta,p=e.split(b'\t',1); mode,kind,oid=meta.split()
            if kind==b'blob': self.entries[p.decode()]=oid.decode()
        self.proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
        self.cache={}
    def read(self,path):
        oid=self.entries.get(path)
        if oid is None: return None
        if oid not in self.cache:
            self.proc.stdin.write((oid+'\n').encode());self.proc.stdin.flush()
            h=self.proc.stdout.readline().split(); n=int(h[2]); b=self.proc.stdout.read(n);self.proc.stdout.read(1)
            self.cache[oid]=b
        return self.cache[oid]
    def text(self,p): return (self.read(p) or b'').decode(errors='replace')

def main():
    a=argparse.ArgumentParser();a.add_argument('--revision',default='HEAD');a.add_argument('--controls-only',action='store_true');args=a.parse_args()
    rev=subprocess.check_output(['git','rev-parse',args.revision],text=True).strip();g=Git(rev)
    if args.controls_only:
        c=run_controls(g);OUT.joinpath('NKT_CHECKER_CONTROLS.json').write_text(json.dumps(c,indent=2)+'\n');assert all(x['pass'] for x in c.values());print(json.dumps({k:v['pass'] for k,v in c.items()}));return
    ledger='evidence/ledger19-20261108/NKN_LEDGER.json.xz'
    d=json.loads(lzma.decompress(g.read(ledger)))
    rows=[r for r in d['rows'] if r['status']=='CLOSED']
    pending=[]
    for dr,pre in [('circle-points-20261108','NKM'),('terminal4-20261108','NKI'),('batch-merkle3-20261108','NKL')]:
        p=f'evidence/{dr}/{pre}_CLOSED.json'; val=json.loads(g.read(p));pending.append({'path':p,'sha256':sha(g.read(p)),'data':val})
    lean=[p for p in g.entries if p.endswith('.lean')]
    bymodule=collections.defaultdict(list)
    for p in lean:
        bymodule[pathlib.PurePosixPath(p).stem].append(p)
    # A conservative import closure: retain all tracked candidates for ambiguous modules.
    seeds=collections.defaultdict(set)
    for r in rows:
        for root in r.get('root_owners',[]): seeds[root['owner_module']].add(r['row'])
        if r.get('owner_module'):seeds[r['owner_module']].add(r['row'])
    for packet in pending:
        v=packet['data'];dr=str(pathlib.PurePosixPath(packet['path']).parent)
        funcs=v.get('functions',v.get('rows',[]))
        for r in funcs:
            if not isinstance(r,dict):continue
            for root in r.get('roots',r.get('lean_roots',r.get('kernel_roots',[]))):
                if isinstance(root,str): seeds[root.split('.')[0]].add('PENDING:'+str(r.get('row',r.get('function'))))
        # Include every top-level candidate module, even if the packet has another schema.
        for p in lean:
            if str(pathlib.PurePosixPath(p).parent)==dr: seeds[pathlib.PurePosixPath(p).stem].add('PENDING:'+dr)
    recorded_imports={}; import_receipts=[]
    for dr,pre in [('ledger19-20261108','NKN'),('circle-points-20261108','NKM'),('terminal4-20261108','NKI'),('batch-merkle3-20261108','NKL')]:
        ip=f'evidence/{dr}/{pre}_EXPECTED_IMPORTS.jsonl'
        import_receipts.append({'path':ip,'sha256':sha(g.read(ip))})
        for ln in g.text(ip).splitlines():
            entry=json.loads(ln);recorded_imports.setdefault(entry['module'],set()).update(entry['imports'])
    imports={}; paths={};unresolved=set(); queue=list(seeds);seen=set()
    while queue:
        m=queue.pop()
        if m in seen:continue
        seen.add(m)
        candidates=bymodule.get(m.split('.')[-1],[])
        if '.' in m:
            suffix=m.replace('.','/')+'.lean'; exact=[p for p in candidates if p.endswith(suffix)]
            candidates=exact
        paths[m]=candidates
        if not candidates:unresolved.add(m)
        deps=set(recorded_imports.get(m,()))
        if m not in recorded_imports:
            for p in candidates:
                clean=re.sub(r'/\-.*?\-/|--[^\n]*','',g.text(p),flags=re.S)
                deps.update(re.findall(r'(?m)^import\s+([^\s/]+)',clean))
        imports[m]=sorted(deps);queue.extend(deps-seen)
    # Propagate row labels through the finite graph.
    labels={m:set(seeds.get(m,())) for m in seen};q=collections.deque(m for m in seen if labels[m])
    while q:
        m=q.popleft()
        for dep in imports.get(m,[]):
            old=len(labels[dep]);labels[dep].update(labels[m])
            if old!=len(labels[dep]):q.append(dep)
    reached={p for ps in paths.values() for p in ps}
    emissions=[p for p in g.entries if p.endswith('/Funs.lean') or p.endswith('/Funs.lean.xz')]
    # Include renamed generated modules recognized by source annotations.
    extra=[]
    for p in sorted(reached):
        if p in emissions:continue
        t=g.text(p)
        if re.search(r"Source: '[^']+\.rs', lines",t) and re.search(r'(?m)^def ',t):extra.append(p)
    audit=[];flagged=[]
    for p in sorted(set(emissions+extra)):
        b=g.read(p)
        if p.endswith('.xz'):b=lzma.decompress(b)
        text=b.decode(errors='replace'); found=sites(text)
        decls=list(re.finditer(r'(?m)^(?:(?:noncomputable|private|protected) )?(def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(]+)',text))
        for di,dm in enumerate(decls):
            if dm.group(1)!='def':continue
            end=decls[di+1].start() if di+1<len(decls) else len(text)
            comment_start=text.rfind('/--',0,dm.start()); comment_end=text.find('-/',comment_start) if comment_start>=0 else -1
            comment=text[comment_start:comment_end+2] if 0<=comment_start<comment_end<dm.start() else ''
            sm=re.search(r"Source: '([^']+)', lines (\d+):(\d+)-(\d+):(\d+)",comment)
            symbol=re.search(r'\[([^\]]+)\]',comment)
            source=sm.group(1) if sm else None;lo,hi=(int(sm.group(2)),int(sm.group(4))) if sm else (None,None)
            startline=text.count('\n',0,dm.start())+1;endline=text.count('\n',0,end)+1
            f=[x for x in found if startline<=x['line']<endline]
            key=FROZEN+':'+source if source else None
            if key and key not in frozen_cache:
                z=subprocess.run(['git','show',key],capture_output=True);frozen_cache[key]=z.stdout if z.returncode==0 else None
            sb=frozen_cache.get(key);span=b'\n'.join(sb.splitlines()[lo-1:hi])+b'\n' if sb is not None else None
            rec={'rust_symbol':symbol.group(1) if symbol else None,'definition':dm.group(2),'source_path':source,'source_lines':[lo,hi] if sm else None,
                 'frozen_body_sha256':sha(span) if span is not None else None,'frozen_hash_scope':'emitter source line span (inclusive), not normalized ledger body',
                 'emission_path':p,'emission_sha256':sha(b),'emitted_definition_sha256':sha(text[dm.start():end].encode()),'emission_line':startline,
                 'in_conservative_import_closure':p in reached,'verdict':'CANDIDATE_REVIEW' if f else 'NO_CHECKER_PATTERN',
                 'sites':f,'source_annotation_status':'FROZEN_PATH_AVAILABLE' if sb is not None else 'REFERENCE_OR_UNMAPPED'}
            audit.append(rec)
        if found:flagged.append({'path':p,'sha256':sha(b),'in_conservative_import_closure':p in reached,'sites':found})
    controls_path='evidence/batch-merkle-20261108/NJS_emitted/raw/NJS_Extract/Funs.lean'
    controls=run_controls(g)
    result={'schema':1,'audit_revision':rev,'frozen_revision':FROZEN,'ledger_sha256':sha(g.read(ledger)),
       'closed_rows':len(rows),'pending_inputs':pending,'coverage_semantics':'Conservative import closure retains every tracked candidate for ambiguous module names. All tracked Funs emissions also scanned as a superset. NO_CHECKER_PATTERN is not a general semantic fidelity proof.',
       'functions':audit,'controls':controls,'counts':{'emission_files':len(emissions),'renamed_emissions':len(extra),'functions':len(audit),'flagged_files':len(flagged),'reached_modules':len(seen),'reached_paths':len(reached)},
       'unresolved_imports':sorted(unresolved),'recorded_import_receipts':import_receipts}
    # Exact file-byte duplicates are aliases, never separate semantic verdicts.
    files={}; unique={}
    for rec in audit:
        eh=rec['emission_sha256'];files.setdefault(eh,[]).append(rec['emission_path'])
        key=(eh,rec['definition'],rec['emission_line'])
        if key in unique:
            unique[key]['in_conservative_import_closure'] |= rec['in_conservative_import_closure']
        else:unique[key]=rec
    result['emission_aliases']={h:sorted(set(ps)) for h,ps in files.items()}
    result['functions']=list(unique.values());result['counts']['distinct_file_definition_occurrences']=len(unique)
    sup=(json.dumps(result,separators=(',',':'))+'\n').encode(); OUT.joinpath('NKT_SUPERSET.json.xz').write_bytes(lzma.compress(sup,preset=6));OUT.joinpath('NKT_SUPERSET.json.sha256').write_text(sha(sup)+'\n')
    result['functions']=[r for r in result['functions'] if r['in_conservative_import_closure'] or r['emission_path']==controls_path]
    result['counts']['main_audit_occurrences']=len(result['functions'])
    OUT.joinpath('NKT_AUDIT.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    OUT.joinpath('NKT_SITES.json').write_text(json.dumps(flagged,indent=2)+'\n')
    ib=(json.dumps({'modules':{m:{'paths':paths[m],'imports':imports[m],'rows':sorted(labels[m])} for m in sorted(seen)}},separators=(',',':'))+'\n').encode(); OUT.joinpath('NKT_IMPORTS.json.xz').write_bytes(lzma.compress(ib,preset=6)); OUT.joinpath('NKT_IMPORTS.json.sha256').write_text(sha(ib)+'\n')
    print(json.dumps({'counts':result['counts'],'controls_batch':controls['batch_tree'],'unresolved_imports':len(unresolved)}))
frozen_cache={}
if __name__=='__main__':main()
