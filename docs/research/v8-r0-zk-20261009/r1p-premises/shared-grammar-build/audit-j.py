import hashlib,json,pathlib,re
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019'); H=J.parent/'r1-privacy-build-integration-20261019'
man=json.loads((J/'evidence/manifest-5-shared-grammar.json').read_text()); env=json.loads((H/'env/J.json').read_text()); libdirs=env['LEAN_PATH'].split(':')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
missing=[]; mismatch=[]; objects_missing=[]
for e in man['order']:
 p=J/'sources'/(e['module'].replace('.','/')+'.lean'); o=J/'objects'/(e['module'].replace('.','/')+'.olean')
 if not p.exists(): missing.append(e['module'])
 elif sha(p)!=e['sha256']:mismatch.append(e['module'])
 if not o.exists():objects_missing.append(e['module'])
libs_missing=[m for m in man['libraries'] if not any((pathlib.Path(d)/(m.replace('.','/')+'.olean')).exists() for d in libdirs)]
rs=[json.loads(l) for l in (J/'evidence/shared-grammar-attempts-6400-6449.jsonl').read_text().splitlines()]
allowed={'propext','Classical.choice','Quot.sound'}; bad=[]
for r in rs:
 if r['exit']!=0:continue
 for line in r['axioms']:
  ax=re.search(r'\[([^\]]*)\]',line)
  if ax and not set(x.strip() for x in ax.group(1).split(',') if x.strip())<=allowed:bad.append([r['attempt'],line])
objs=[]
for m in ['SharedBinaryRecordGrammar','R1Z.SharedGrammarBridgeBin','BinSharedGrammarBridge']:
 p=J/'objects'/(m.replace('.','/')+'.olean');objs.append({'module':m,'object_sha256':sha(p),'size_bytes':p.stat().st_size})
r={'manifest_sha256':sha(J/'evidence/manifest-5-shared-grammar.json'),'source_revision_parent':man['repo_revision'],'manifest_module_count':len(man['order']),'missing_sources':missing,'source_mismatches':mismatch,'missing_objects':objects_missing,'missing_libraries':libs_missing,'nonstandard_axioms':bad,'successful_attempts':[x['attempt'] for x in rs if x['exit']==0],'fingerprint_refusals':[x['attempt'] for x in rs if x['exit']==67],'successful_axiom_audits':sum(len(x['axioms']) for x in rs if x['exit']==0),'new_objects':objs}
print(json.dumps(r,indent=2));assert not any([missing,mismatch,objects_missing,libs_missing,bad])
