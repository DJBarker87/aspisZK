import pathlib,json,subprocess,collections,hashlib,sys,re
out=pathlib.Path(sys.argv[1]); rows=[]; gdir=out/'graphs';gdir.mkdir(exist_ok=True)
for p in sorted((out/'target').rglob('*.kani-metadata.json')):
 for h in json.loads(p.read_text()).get('proof_harnesses',[]):
  f=pathlib.Path(h['goto_file']);f=f.with_name(f.name.replace('.symtab.out','.out'))
  if not f.exists():continue
  cmd=['/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','--call-graph',str(f)]
  r=subprocess.run(cmd,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stderr
  edges=[l.split(' -> ',1) for l in r.stdout.splitlines() if ' -> ' in l];adj=collections.defaultdict(list)
  for a,b in edges:adj[a].append(b)
  root=h['mangled_name']
  q=collections.deque([root]);paths={root:[root]}
  while q:
   a=q.popleft()
   for b in adj[a]:
    if b not in paths:paths[b]=paths[a]+[b];q.append(b)
  # Keep an alternative path excluding allocation growth/shrink nodes, so a
  # shortest path through an allocator cannot hide a direct typed copy.
  nq=collections.deque([root]);non_growth={root:[root]}
  while nq:
   a=nq.popleft()
   for b in adj[a]:
    if b not in non_growth and not re.search(r'grow|shrink|realloc',b):
     non_growth[b]=non_growth[a]+[b];nq.append(b)
  label=h['pretty_name'].replace('::','__')+'-'+hashlib.sha256(f.read_bytes()).hexdigest()[:12];gp=gdir/(label+'.txt');gp.write_text(r.stdout)
  s=(out/'package'/h['original_file']).read_text() if (out/'package'/h['original_file']).exists() else ''
  lines=s.splitlines();body='\n'.join(lines[h['original_start_line']-1:h['original_end_line']])
  rows.append(dict(harness=h['pretty_name'],metadata=h,goto_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),graph_file=str(gp.relative_to(out)),graph_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),graph_target=cmd,nongrowth_copy_paths={b:non_growth[b] for b in ['memcpy','memmove'] if b in non_growth},copy_predecessors=[dict(caller=a,builtin=b) for a,bs in adj.items() if a in paths for b in bs if b in ['memcpy','memmove']],reachable_symbols=sorted(paths),copy_paths={x:paths[x] for x in ['memcpy','memmove'] if x in paths},source_body=body,source_sha256=hashlib.sha256(s.encode()).hexdigest()))
(out/'goto-scan.json').write_text(json.dumps(rows,indent=2)+'\n')
print(out.name,len(rows),[(x['harness'],list(x['copy_paths'])) for x in rows],flush=True)
