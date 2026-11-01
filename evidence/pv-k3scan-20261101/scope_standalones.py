"""Separate selected standalone compiler inputs from the all-package freeze inventory.
No source is invented or edited: every selected byte is pinned by that run's manifest.
"""
from pathlib import Path
import json,lzma,subprocess,hashlib,re,sys,tomllib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E/'classifier'));from NEH_scan import classify
rows=json.loads(lzma.decompress((E/'CREDITS.raw.json.xz').read_bytes()));manifests=json.loads((E/'KMX-MANIFEST-RECOVERY.json').read_text());idx=json.loads((E/'SOURCE_INDEX.json').read_text());out=[]
for x in rows:
 if '/pv-kstub-' not in x['path'] or x['path'].split('/')[-2] not in ['K04','K06','K08','K12','K14']:continue
 r=x['receipt'];cmd=r['target'];manifest=cmd[cmd.index('--manifest-path')+1];pkg=Path(manifest).parent.name;assert pkg in ('cb','cblib')
 rp=str(Path(x['path']).parent/'source-manifest.json');raw=subprocess.check_output(['git','show',x['revision']+':'+rp]);freeze={f['path']:f for f in json.loads(raw)}
 cargo=manifests[pkg+'/Cargo.toml'];assert cargo['sha256']==freeze[pkg+'/Cargo.toml']['sha256'];assert hashlib.sha256(cargo['text'].encode()).hexdigest()==cargo['sha256'];toml=tomllib.loads(cargo['text']);assert toml['lib']['path']=='lib.rs';assert not any(k.endswith('dependencies') or k=='build' for k in toml);assert 'build' not in toml['package']
 names=[pkg+'/lib.rs','KMX_stubs.rs']+(['cb/reference.rs'] if pkg=='cb' else []);src={};hashes={}
 for n in names:
  h=freeze[n]['sha256'];assert h in idx,(n,h);b=(E/'blobs'/(h+'.rs')).read_bytes();assert hashlib.sha256(b).hexdigest()==h;src[n]=b.decode();hashes[n]=h
 for n,t in src.items():
  external_mods=set(re.findall(r'\bmod\s+(\w+)\s*;',t));assert external_mods<=({'reference','KMX_stubs'} if n.endswith('/lib.rs') else set()),(n,external_mods)
  assert not re.search(r'\b(?:aspis_\w+|extern crate (?!alloc|std))',t)
 c=classify(src);assert c['classification']=='UNAFFECTED',c
 out.append({'receipt':x['path'],'harness':x['harness'],'classification':'NOT-EXPOSED','classifier_result':c,'selected_hashes':hashes,'manifest_sha256':cargo['sha256'],'freeze_path':rp,'freeze_sha256':hashlib.sha256(raw).hexdigest(),'compiler_manifest':manifest,'module_closure':'Standalone package has no dependencies/build script; all out-of-line modules are KMX_stubs and, for cb only, reference. Entire recovered Rust module texts pass NEH_scan, so no custom macro or hidden include requires expansion. Standard library/tool semantics remain separate.','excluded_inventory':'Other prepared packages native/core, split and native fixtures are not dependencies of this standalone package. Their inputs remain in the raw audit and are not treated as its harness/stub/oracle closure.'})
assert len(out)==5
(E/'SELECTED-STANDALONE-SCOPES.json').write_text(json.dumps(out,indent=2)+'\n');print('5 exact standalone module closures pass the unchanged classifier')
