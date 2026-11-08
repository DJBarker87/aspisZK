"""Recover an explicitly FAILED receipt from finalized host time/report files."""
import json,pathlib,subprocess,shlex
E=pathlib.Path(__file__).parent;V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence'
code=r'''
import pathlib,json,re,shlex,hashlib
V=pathlib.Path('HOST');E=V/'evidence';p=E/'receipt-56594.json';assert not p.exists()
t=(E/'time-56594.log').read_text();u=json.load(open(E/'UNION_AUDIT-56594.json'));assert not u['strict_pass'] and u['root_count']==2950
r=dict(attempt=56594,target='audit',source_revision=json.load(open(V/'PLAN.json'))['revision'],tools_revision='TOOLS',exit=120,accepted=False,recovered=True,recovery_basis='Finalized GNU time status120 and partial UNION_AUDIT, original SSH-dependent controller terminated before writing its receipt; not a pass.',transport_exit=255,capped_scope='pv-lib-56594.scope',root_count=u['root_count'],expected_root_count=4307,time_sha256=hashlib.file_digest(open(E/'time-56594.log','rb'),'sha256').hexdigest(),axioms_summary_based='Partial results only; no strict union pass.')
assert re.search(r'Exit status:\s*120',t)
for l in t.splitlines():
 for k,f in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
  if k in l:r[f]=l.split(k)[1].strip()
 if 'Command being timed:' in l:r['command']=shlex.split(l.split('Command being timed:',1)[1].strip()[1:-1])
p.write_text(json.dumps(r,indent=2));print(json.dumps(r))
'''.replace('HOST',V).replace('TOOLS',subprocess.check_output(['git','rev-parse','5c9b6b294da'],text=True).strip())
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'RECOVERED_RECEIPT-56594.json').write_text(r.stdout);print(r.stdout)
