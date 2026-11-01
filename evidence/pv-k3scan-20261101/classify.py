import pathlib,json,re,sys,collections,lzma,hashlib
E=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(E/'classifier'));from NEH_scan import classify
rs=json.loads((E/'RECOVERED.json').read_text());idx=json.loads((E/'SOURCE_INDEX.json').read_text());bindings=json.loads((E/'inputs/k1-d347-source-bindings.json').read_text());out=[]
for x in rs:
 r=x['receipt']
 if not isinstance(r,dict):continue
 h=x.get('historical_harness') or r.get('harness')
 cmd=r.get('native_command') or r.get('command') or r.get('target',[])
 if isinstance(cmd,list) and '--harness' in cmd:h=cmd[cmd.index('--harness')+1]
 elif not h and isinstance(cmd,str):
  m=re.search(r'--harness\s+([\w:]+)',cmd)
  if m:h=m[1]
 elif not h and isinstance(r.get('target'),str):h=r['target']
 ex=r.get('exit_status',r.get('exit'));success=str(ex)=='0' or ('k1_index' in x)
 if not h or '--only-codegen' in str(cmd) or not success:continue
 hh=x.get('recorded_rust_hashes',{}).copy();sources={};matched={};missing=[]
 if 'k1_index' in x:
  for b in bindings:
   if x['k1_index'] not in b['indices']:continue
   for f in b['files']:
    if f['path'].endswith(('.rs','.rs.txt')):
     # codegen sources supplement closure; association is retained as the earlier audit's structural input argument.
     hh.setdefault('k1-'+b['run']+':'+f['path'],f['sha256'])
 for n,sh in hh.items():
  if sh in idx:
   sources[n]=(E/'blobs'/(sh+'.rs')).read_text(errors='replace');matched[n]={'sha256':sh,'provenance':idx[sh][0]}
  else:missing.append({'source':n,'sha256':sh})
 c=classify(sources,missing)
 stubs=sorted(set(t.strip() for s in sources.values() for t in re.findall(r'#\[kani::stub(?:_verified)?\((.*?)\)\]',s,re.S)))
 writable=[a for a in c['static_sites'] if re.search(r'\bstatic\s+mut\s|\bstatic\s+\w+\s*:\s*(?:Atomic|Cell|RefCell|UnsafeCell|Mutex|Once)',a['text'])]
 cl='UNAFFECTED' if c['classification']=='UNAFFECTED' else 'OPEN' if missing or c['macro_sources'] or not sources else 'EXPOSED'
 # Missing inputs and unexpanded macros keep the receipt OPEN, even when a static is also present.
 x.update(harness=h,raw_classifier=c,classification=cl,matched_rust=matched,missing_rust=missing,stubs=stubs,writable_static_candidates=writable)
 out.append(x)
payload=(json.dumps(out,indent=2)+'\n').encode();(E/'CREDITS.raw.json.xz').write_bytes(lzma.compress(payload,preset=1));(E/'CREDITS.raw.json.sha256').write_text(hashlib.sha256(payload).hexdigest()+'\n')
print('PASS observations',len(out),'classification',dict(collections.Counter(x['classification'] for x in out)))
for x in out:
 if x['classification']=='EXPOSED':print(x['path'],x['harness'],'writable',len(x['writable_static_candidates']),'missing',len(x['missing_rust']),'macros',len(x['raw_classifier']['macro_sources']))
