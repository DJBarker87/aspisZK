from pathlib import Path
import json,re,hashlib,subprocess
E=Path('evidence/pv-fscan-20261028');a=json.loads((E/'native-evidence-index.json').read_text());man={x['path']:x for x in json.loads((E/'historical-manifests.json').read_text())};graphs={x['path']:x for x in json.loads((E/'historical-resolution.json').read_text()) if x.get('exit')==0};graphs.update({x['path']:x for x in json.loads((E/'historical-resolution-recovery.json').read_text()) if x.get('exit')==0})
for i in a['items']:
 m=re.search(r'--manifest-path[ =]([^ ]+)',i['command']);path=m[1] if m else None
 if path in man:
  raw=json.loads(Path(i['path']).read_text());inputs=raw.get('inputs',raw.get('source_files',{})) if isinstance(raw,dict) else {};pin=inputs.get(path)
  h=pin.get('sha256') if isinstance(pin,dict) else pin if isinstance(pin,str) else None
  i['historical_manifest']=dict(path=path,collected_sha256=man[path]['sha256'],receipt_sha256=h,receipt_hash_matches=h==man[path]['sha256'],source_scope='historical only on hash match; otherwise current retained manifest is diagnostic')
  if path in graphs:i['retained_manifest_resolved_features']=graphs[path]['features']
  i['retained_manifest_profiles']={k:v for k,v in __import__('tomllib').loads(man[path]['text']).get('profile',{}).items()}
 i['body_credit']='none inferred from this inventory entry; row decisions and original success/domain/control association remain separate'
# Avoid repeating full graphs thousands of times: stable references retain every per-crate feature list once.
for i in a['items']:
 if 'retained_manifest_resolved_features' in i:
  del i['retained_manifest_resolved_features'];i['resolved_feature_graph_ref']='historical-resolution.json or historical-resolution-recovery.json#'+i['historical_manifest']['path']
(E/'native-evidence-index.json').write_text(json.dumps(a,indent=2)+'\n')
facts=[]
for lane in a['lanes']:
 for top in ['tools','evidence']:
  root=Path(top)/lane
  if not root.exists():continue
  for p in root.rglob('*'):
   if not p.is_file() or p.suffix not in ['.py','.sh','.toml'] or p.stat().st_size>1000000:continue
   lines=p.read_text(errors='replace').splitlines();found=[dict(line=n,text=s) for n,s in enumerate(lines,1) if re.search(r'cargo |rustc|--features|profile\.(?:dev|release)|overflow-checks|debug-assertions|CARGO_PROFILE_|ct-host-prover|\b-O\b',s)]
   if found:facts.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=found))
(E/'configuration-source-facts.json').write_text(json.dumps(facts,indent=2)+'\n')
print('Enriched',len(a['items']),'commands;',len(facts),'configuration source files')
