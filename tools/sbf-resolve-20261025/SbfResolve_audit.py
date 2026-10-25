"""Offline receipt/graph consistency and lexical trace census, not a closure parser."""
import collections,hashlib,json,pathlib,re,resource,shlex,subprocess,time
B=pathlib.Path('evidence/sbf-resolve-20261025');T=pathlib.Path('tools/sbf-resolve-20261025');t=time.monotonic();checks=[];inputs={}
def check(x,label):
 if not x:raise AssertionError(label)
 checks.append(label)
def read(name):
 p=B/name;b=p.read_bytes();inputs[str(p)]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};return b
def load(name):return json.loads(read(name))
def git(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
def trace_census(name):
 raw=read(name).decode();pending={};events=[]
 for line in raw.splitlines():
  match=re.match(r'^(\d+) (.*)$',line);check(bool(match),'trace line has PID')
  pid,s=match.groups()
  if '<unfinished ...>' in s:
   check(pid not in pending,'one pending lexical syscall per PID');pending[pid]=s.replace('<unfinished ...>','');continue
  if s.startswith('<... '):
   check(pid in pending and 'resumed>' in s,'matched lexical continuation');s=pending.pop(pid)+s.split('resumed>',1)[1]
  events.append(dict(pid=pid,text=s))
 check(not pending,'no unmatched lexical continuations')
 opens=[];paths=[];execs=[]
 for event in events:
  s=event['text'];m=re.search(r'openat\(AT_FDCWD, "([^"\\]*)", .*\)\s+= (\d+)',s)
  if m:opens.append(m[1])
  paths+=re.findall(r'"(/[^"\\]*)"',s)
  if s.startswith(('execve(','execveat(')):execs.append(event)
 source='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src/'
 source_mutations=[e for e in events if source in e['text'] and (re.search(r'\b(O_WRONLY|O_RDWR|O_CREAT|O_TRUNC)\b',e['text']) or re.match(r'(unlink|rename|chmod|chown|utime|truncate|mkdir|rmdir|symlink|link)',e['text']))]
 return dict(successful_absolute_openat_paths=sorted(set(opens)),absolute_quoted_paths=sorted(set(paths)),exec_records=execs,source_mutation_candidates=source_mutations,lexical_events=len(events),limitations='lexical census only; no fd/cwd/mmap/credential/syscall/input immutability or cache closure proof')
queries={}
for number in [1,2]:
 label=f'query-{number}';j=load(f'SbfResolve-{label}.stdout');req=load(f'SbfResolve-{label}-request.json');tr=load(f'SbfResolve-{label}-transport.json')
 check(j['exit']==j['cargo_exit']==tr['exit']==0,label+' exit0')
 check(j['helper_sha256']==hashlib.sha256(req['host_command'][-1].encode()).hexdigest(),label+' actual -c helper source')
 check(req['host_command'][-1].encode()==git(req['revision'],'tools/sbf-resolve-20261025/SbfResolve_host.py'),label+' committed helper bytes')
 check(tr['transport'][-1]==' '.join(shlex.quote(x) for x in req['host_command']),label+' exact shell quoted argv')
 check(j['tools_before']==j['tools_after'] and j['runtime_before']==j['runtime_after'],label+' tool/runtime pins unchanged')
 check(j['sampled_aggregate_rss_bytes']<512*1024**2 and j['swap']==j['sampled_aggregate_swap_bytes']==0,label+' RSS/swap bound')
 check(j['admission']['sum_memory_max']+512*1024**2<55*1024**3,label+' bounded prep reservations')
 check(j['admission']['mem_available']>=7*1024**3+512*1024**2,label+' control availability')
 for kind in ['stdout','trace']:
  b=read('SbfResolve-raw-'+label+'.'+kind);r=j['outputs'][kind];check(len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],label+' '+kind+' seal')
 check(j['guard']['sha256']==hashlib.sha256(T.joinpath('SbfResolve_guard.py').read_bytes()).hexdigest(),label+' guard pin')
 check(j['parent_pins_before']==j['parent_pins_after'],label+' parent/lock/wrapper pins unchanged')
 check(j['source_pins_after']==load('SbfResolve-init.stdout')['source_pins'],label+' reviewed manifest pins unchanged')
 data=load('SbfResolve-raw-'+label+'.stdout');check(len(data['packages'])==j['metadata_summary']['packages'],label+' package count')
 c=trace_census('SbfResolve-raw-'+label+'.trace');check(not c['source_mutation_candidates'],label+' no lexical source mutation candidate')
 check(not any('/home/dombarker/.cargo/' in p or '/home/dombarker/.rustup/' in p for p in c['absolute_quoted_paths']),label+' no global Cargo/rustup path in trace')
 config=[p for p in c['successful_absolute_openat_paths'] if p.endswith(('/config','/config.toml','/credentials','/credentials.toml')) and '/registry/index/' not in p]
 check(config==[j['loaded_config_candidates'][0]['path']],label+' only own Cargo config opened')
 c['loaded_config_open_paths']=config
 check(len(c['exec_records'])==(1 if number==1 else 7),label+' exec lexical census')
 queries[number]=dict(receipt=j,metadata=data,census=c)
check(queries[1]['metadata']['resolve'] is None and len(queries[1]['receipt']['compiler_queries'])==0,'query1 null resolve, no compiler')
q=queries[2];check(q['metadata']['resolve'] is not None,'query2 actual graph')
check(len(q['receipt']['compiler_queries'])==3 and all(r['allowed'] for r in q['receipt']['compiler_queries']),'only three approved compiler queries')
raw=read('SbfResolve-raw-compiler-queries.jsonl');check([json.loads(x) for x in raw.splitlines()]==q['receipt']['compiler_queries'],'raw compiler argv records')
u=load('SbfResolve-universe-v5.stdout');locked={(r['name'],r['version']):r for r in u['locked_universe']};check(len(locked)==428 and u['download_bytes']==0 and not u['attempts'],'428 public cache archives/no network')
old=json.loads(git('65c4082110','evidence/sbf-inputs-20261024/packages.json'));oldset={tuple(r['crate'].rsplit('-',1)) for r in old};check(len(oldset)==123,'reused123 distinct')
returned={(p['name'],p['version']) for p in q['metadata']['packages'] if p['source']};check(len(returned)==344 and returned<=locked.keys(),'344 graph registry packages frozen')
opens=q['census']['successful_absolute_openat_paths'];paths=q['census']['absolute_quoted_paths'];idxprefix='/cargo/registry/index/';srcprefix='/cargo/registry/src/';arcprefix='/cargo/registry/cache/'
source_opened={p.split(srcprefix)[1].split('/')[1] for p in opens if srcprefix in p};archive_opened={pathlib.PurePosixPath(p).name.removesuffix('.crate') for p in opens if arcprefix in p and p.endswith('.crate')};probed={pathlib.PurePosixPath(p).name.removesuffix('.crate') for p in paths if arcprefix in p and p.endswith('.crate')};index_opened={p for p in opens if idxprefix in p and '/.cache/' in p}
check(len(source_opened)==len(archive_opened)==371,'371 source/archive package names observed opened')
check(len(index_opened)==394 and len(probed)==428,'394 indices and428 archive presence paths observed')
nodes={n['id']:n for n in q['metadata']['resolve']['nodes']};packages={p['id']:p for p in q['metadata']['packages']};root=q['metadata']['resolve']['root'];todo=[root];reachable=set()
while todo:
 x=todo.pop()
 if x in reachable:continue
 check(x in nodes,'reachable graph node exists');reachable.add(x);todo.extend(nodes[x]['dependencies'])
reachregistry={(packages[x]['name'],packages[x]['version']) for x in reachable if packages[x]['source']};check(len(reachable)==178 and len(reachregistry)==174,'graph root reachability')
rows=[]
for key,r in sorted(locked.items()):
 crate='-'.join(key);check(r['checksum']==r['archive']['sha256'],'archive checksum '+crate)
 rows.append(dict(name=key[0],version=key[1],checksum=r['checksum'],archive=r['archive'],index=r['index'],initial123=key in oldset,in_returned_graph=key in returned,in_root_reachable_graph=key in reachregistry,source_package_opened=crate in source_opened,archive_opened=crate in archive_opened,archive_presence_path_observed=crate in probed,provenance='reused reviewed123' if key in oldset else 'new private copy from checksum-matched public .crate cache; no downloads'))
summary=dict(cargo_cli_used=2,cargo_cli_allocation=2,crate_compilations=0,build_script_executions=0,proc_macro_executions=0,workspace_members=13,query1=dict(packages=13,resolve=None),query2=dict(packages=357,registry_packages=344,graph_nodes=357,scope='whole workspace/default features/dev deps; sbpf-solana-solana filter, also host metadata discovery',root_features=nodes[root]['features'],root_reachable_packages=178,root_reachable_registry=174,root_reachability_limit='computed from workspace-unified metadata graph; not selected compilation units or independently resolved root features'),prepared_registry=428,prepared_indices=394,initial_registry=123,additional_prepared=305,observed_source_archive_opens=371,observed_index_opens=394,archive_presence_paths=428,graph_beyond_initial=len(returned-oldset),root_graph_beyond_initial=len(reachregistry-oldset),prepared_not_returned=len(locked.keys()-returned),prepared_without_source_open=len(locked)-len(source_opened),required_limit='Observed accessed/returned sets for this execution, not a minimal necessity proof. All428 archive availability paths were probed; no counterfactual missing-cache run.305 is not selected-build necessity.',cache_manifest=load('SbfResolve-raw-export-summary.json')['remote_manifest'],target_entries=load('SbfResolve-raw-export-summary.json')['target_entries'],origin_field_correction='universe receipt origin=reused123 means existed on that continuation, including partial earlier copies; authoritative original123 association is packages.json and this per-package initial123 flag',helper_field_correction='receipt helper seals the initial staged reference file; actual executed helper is -c text sealed by helper_sha256 and exact request argv, verified against source_revision',runtime_limit='11 selected tool/driver/loader/DSO paths pinned before/after; Python stdlib/pyc and full dynamic file closure not newly sealed. Prior full archive/source evidence reused explicitly. Ordinary same-uid stage is not immutable private execution.',trace_limit=q['census']['limitations'],theorem_statements_before_after='unchanged; no premises added/discharged; no new trust assumption',print_axioms='N/A',security_targets='both not established',reserved='final Kani59/60',rows=rows)
(B/'SbfResolve-sets.json').write_text(json.dumps(summary,indent=2)+'\n')
(B/'SbfResolve-trace-census.json').write_text(json.dumps({str(n):r['census'] for n,r in queries.items()},indent=2)+'\n')
uusage=resource.getrusage(0);receipt=dict(command=['python3','-B','tools/sbf-resolve-20261025/SbfResolve_audit.py'],exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=uusage.ru_maxrss,swap=uusage.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),helper_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),checks=len(checks),inputs=inputs,print_axioms='N/A: offline data audit, no theorem')
(B/'SbfResolve-audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='rows'},indent=2));print(json.dumps({k:v for k,v in receipt.items() if k!='inputs'},indent=2))
