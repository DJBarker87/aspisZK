#!/usr/bin/env python3
"""Read/hash accepted current selected-read packet; never invoke Lean."""
from pathlib import Path
import json,hashlib,tarfile,re
from archive_parts import accepted_archive
ROOT=Path(__file__).resolve().parents[2];E=ROOT/'evidence/selected-read-current-20261018';M=json.loads((E/'packet-manifest.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def inverse(current,diff):
 lines=current.splitlines(True);out=[];at=0;ds=diff.splitlines(True);i=2
 while i<len(ds):
  mat=re.match(r'@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@',ds[i]);assert mat,ds[i];start=int(mat[1])-1;i+=1;out+=lines[at:start];at=start
  while i<len(ds) and not ds[i].startswith('@@'):
   q=ds[i];i+=1
   if q.startswith('\\'):continue
   assert q[0] in ' +-'
   if q[0] in ' +':assert lines[at]==q[1:],(lines[at],q);at+=1
   if q[0] in ' -':out.append(q[1:])
 out+=lines[at:];return ''.join(out)
with accepted_archive(E,M) as (archive,member_manifest), tarfile.open(fileobj=archive,mode='r:gz') as t:
 actual=t.getmembers();assert len(actual)==len(member_manifest)
 for member,pin in zip(actual,member_manifest):
  assert member.isfile() and member.name==pin['name'] and member.size==pin['bytes'] and member.type.decode('ascii')==pin['type']
  assert hashlib.file_digest(t.extractfile(member),'sha256').hexdigest()==pin['sha256'],member.name
 sums=json.load(t.extractfile('SHA256SUMS.json'));members=t.getnames();assert set(members)==set(sums)|{'SHA256SUMS.json'}
 for n,h in sums.items():assert hashlib.file_digest(t.extractfile(n),'sha256').hexdigest()==h,n
 get=lambda n:t.extractfile(n).read();load=lambda n:json.loads(get(n))
 manifest=load('sources/SOURCE-MANIFEST.json');rs=[load(n) for n in sums if n.startswith('successful-targets/')];assert len(rs)==215==len(manifest['modules'])
 standard={'propext','Classical.choice','Quot.sound'}
 for r in rs:
  assert r['exit_status']==0 and r['axioms']['passed'] and r['process_swaps']==0
  assert all(set(v['axioms'])<=standard for v in r['axioms']['reports'])
  assert r['key']['source_sha256']==sha(get('sources/'+manifest['modules'][r['target']]['stage_as']))
  for suffix,o in r['objects'].items():assert sums['objects/'+r['target'].replace('.','/')+suffix]==o['sha256']
 assert sum(len(r['axioms']['reports']) for r in rs)==1540
 assert sum(not r['axioms']['requested_count'] for r in rs)==17
 for a in load('proof-import-split-audit.json'):
  current=get('split-sources/'+a['module'].replace('.','/')+'.lean').decode();assert sha(current.encode())==a['split_source_sha256'];assert sha(inverse(current,a['source_diff']).encode())==a['original_source_sha256']
  if 'new_core' in a:
   core=get('split-sources/'+a['new_core']+'.lean').decode();assert sha(core.encode())==a['new_core_sha256']
   start=core.index('structure Public ' if a['new_core']=='R1UnifiedSamplerPublic' else 'def sigma ');end=core.index('\n#print axioms',start);decl=core[start:end].rstrip()+'\n';assert sha(decl.encode())==a['exact_original_declaration_sha256']
 repairs=load('proof-normalization-repairs.json');byhash={h:n for n,h in sums.items() if n.endswith('.lean')}
 for a in repairs:
  current=get(byhash[a['new_source_sha256']]).decode();old=inverse(current,a['source_diff']);assert sha(old.encode())==a['old_source_sha256']
  if a['module']=='AspisFormal.V6PublishedTheoremInterfaces':
   theorem='theorem output_list_expression_lt_113';assert old[old.index(theorem):old.index(':= by',old.index(theorem))]==current[current.index(theorem):current.index(':= by',current.index(theorem))]
  else:assert current.replace('set_option pp.fullNames true in\n','')==old
print('PASS215 current targets /1540 standard-or-empty reports /17 compile-only; exact split inverses and same-statement/print-only repairs; no compiler invoked')
