#!/usr/bin/env python3
from pathlib import Path
import tarfile,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/source-trace-prerequisites-20261018';m=json.loads((E/'packet-manifest.json').read_text());p=E/m['archive'];sha=lambda b:hashlib.sha256(b).hexdigest();assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==m['archive_sha256']
with tarfile.open(p) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert set(t.getnames())==set(sums)|{'SHA256SUMS.json'}
 for n,h in sums.items():assert hashlib.file_digest(t.extractfile(n),'sha256').hexdigest()==h,n
 load=lambda n:json.load(t.extractfile(n));get=lambda n:t.extractfile(n).read();rs=[load(n) for n in sums if n.startswith('successful-targets/')];manifest=load('sources/SOURCE-MANIFEST.json');assert len(rs)==7==len(manifest['modules']) and sum(len(r['axioms']['reports']) for r in rs)==26
 for r in rs:
  assert r['exit_status']==0 and r['axioms']['passed'] and r['process_swaps']==0
  assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axioms']['reports'])
  assert r['key']['source_sha256']==sha(get('sources/'+manifest['modules'][r['target']]['stage_as']))
  for suffix,o in r['objects'].items():assert sums['objects/'+r['target'].replace('.','/')+suffix]==o['sha256']
 original=get('original-context/R1UnifiedSemanticRecovery.lean').decode();core=get('sources/R1UnifiedSemanticRecoveryCore.lean').decode();full=get('split-sources/R1UnifiedSemanticRecovery.lean').decode();a=load('typed-core-split-audit.json');context=load('typed-core-context-audit.json');start=original.index('def typed ');end=original.index('\ntheorem typed_before_row',start);cstart=core.index('def typed ');cend=core.index('\n#print axioms',cstart)
 assert original[start:end].strip()==core[cstart:cend].strip();assert sha(original.encode())==a['original_source_sha256'];assert sha(core.encode())==a['core_sha256'];assert full=='import R1UnifiedSemanticRecoveryCore\n'+original[:start]+original[end:]
 assert context['original_namespace_context']==original[:start] and context['new_core_context']==core[:cstart]
 assert context['exact_definition_statement_and_body_equal']
 assert 'SourceAgreement' not in manifest['modules']
print('PASS7 targets/26standard reports; exact typed statement/body/context/inverse and D-derived oracle; no compiler invoked')
