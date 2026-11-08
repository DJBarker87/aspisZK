"""ONE aggregate strict audit of the UNION in one capped scope and one cohort.
Each immutable array-only driver covers a disjoint root batch. The accepted
private importAll walker/collector and the existing runner are unchanged.
"""
import pathlib,json,sys,hashlib,subprocess,re
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';O=V/'objects-canonical';S=V/'sources-canonical';a=int(sys.argv[1]);focus=len(sys.argv)>2 and sys.argv[2]=='focus';assert 56590<=a<=56599
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest();cfg=json.load(open(V/'FINAL_ROOT_BATCHES.json'));expected=json.load(open(V/'AUDIT_ROOTS.json'))['roots'];assert len([r for b in cfg['batches'] for r in b['roots']])==len(expected) and {r for b in cfg['batches'] for r in b['roots']}==set(expected)
statement=json.load(open(E/'STATEMENT_COHERENCE.json'));assert statement['statement_differences']==0 and statement['source_groups']==47 and statement['expr_equal_count']==55
compat=[json.loads(l) for l in (E/'out-56558.log').read_text().splitlines() if l.startswith('{')][-1];assert compat['compatible'] is True
assert sha(V/'run-thread-audit.py')=='463b79c3c3b0b198563684fea65e14cdbe58ac833bc3f24aad93f6268751930a'
driver='PV_LIB_V1_RawAuditNarrow'
assert sha(S/(driver+'.lean'))=='a67e575fd042fb667c3a91754203475994a3ca06cf244cf0277d433db0779f35'
receipt=json.load(open(E/'receipt-56566.json'));assert receipt['accepted']
# Retain the failed buffered 125-root walk before any graph filename is reused.
archive=E/'failed-56590-graphs.json.xz'
if not archive.exists():
 import lzma
 files={p.name:p.read_text() for p in (E/'raw-audit').glob('NEP_pv-thread_*') if p.is_file()}
 with lzma.open(archive,'wt') as f:json.dump(files,f)
 (E/'FAILED_GRAPH_ARCHIVE-56590.json').write_text(json.dumps(dict(files=len(files),sha256=sha(archive))))
# Preserve failed attempt56592 walks before any filename is reused.
archive=E/'failed-56592-graphs.json.xz'
if not archive.exists():
 import lzma
 files={p.name:p.read_text() for p in (E/'raw-audit').glob('NEP_pv-thread_*') if p.is_file()}
 with lzma.open(archive,'wt') as f:json.dump(files,f)
 (E/'FAILED_GRAPH_ARCHIVE-56592.json').write_text(json.dumps(dict(files=len(files),sha256=sha(archive))))
# Preserve transport-aborted56594 raw walks before their filenames are reused.
archive=E/'failed-56594-graphs.json.xz'
if not archive.exists():
 import lzma
 files={p.name:p.read_text() for p in (E/'raw-audit').glob('NEP_pv-thread_*') if p.is_file()}
 with lzma.open(archive,'wt') as f:json.dump(files,f)
 (E/'FAILED_GRAPH_ARCHIVE-56594.json').write_text(json.dumps(dict(files=len(files),sha256=sha(archive))))
selected=[b for b in cfg['batches'] if b['name'] in cfg['focus_batches']] if focus else cfg['batches']
expected=[r for b in selected for r in b['roots']]
selection_dir=V/'root-selections';selection_dir.mkdir(exist_ok=True)
all_results=[];batches=[]
for b in selected:
 payload=json.dumps(dict(modules=b['modules'],roots=b['roots']),sort_keys=True)+'\n'
 selection=selection_dir/(b['name']+'.json')
 if selection.exists():assert selection.read_text()==payload
 else:selection.write_text(payload)
 (E/'raw-audit/V1_ROOT_SELECTION.json').write_text(payload)
 n=b['name'];log=E/f'out-{a}-{n}.log';tim=E/f'time-{a}-{n}.log'
 cmd=['/usr/bin/time','-v','-o',str(tim),'timeout','900','python3',str(V/'run-thread-audit.py'),str(V/'J.json'),str(S/(driver+'.lean'))]
 with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=V)
 out=log.read_text();results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in out.splitlines() if l.startswith('NEP62_RESULT ')]
 valid=(r.returncode==0 and len(results)==len(b['roots']) and {q['root'] for q in results}==set(b['roots']) and all(q['equal'] and set(q['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for q in results))
 rec=dict(selection_sha256=sha(selection),driver_object_sha256=sha(O/(driver+'.olean')),batch=n,exit=r.returncode,accepted=valid,root_count=len(results),command=cmd,source_sha256=sha(S/(driver+'.lean')),axioms_summary_based=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out),log_sha256=sha(log))
 for line in tim.read_text().splitlines():
  for k,f in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
   if k in line:rec[f]=line.split(k)[1].strip()
 batches.append(rec);all_results.extend(results)
 report=dict(attempt=a,source_revision=cfg['cohort'],same_frozen_object_mapping=True,walker_collector_unchanged=True,batches=batches,roots=all_results,focused=focus,strict_pass=not focus and valid and len(all_results)==len(expected),root_count=len(all_results),expected_root_count=len(expected))
 (E/f"{'FOCUSED' if focus else 'UNION'}_AUDIT-{a}.json").write_text(json.dumps(report,indent=2));print(json.dumps({k:rec[k] for k in ['batch','exit','accepted','root_count','wall','peak_rss_kbytes','swaps']}),flush=True)
 if not valid:print(out[-5000:],flush=True);sys.exit(r.returncode or 1)
assert len(all_results)==len(expected) and {r['root'] for r in all_results}==set(expected)
print('FOCUSED_PASS' if focus else 'STRICT_UNION_PASS',len(all_results),'roots; one frozen source/object cohort',flush=True)
