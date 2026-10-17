#!/usr/bin/env python3
"""Append only coherent pinned prefix cache; stage one names-only repair cone."""
from pathlib import Path
import hashlib,json,importlib.util,re,shutil
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-proof-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017');Q=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-callers-c16-20261016/prefix-adapter');W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py');sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r);sha=r.sha
D=json.loads((P/'external-inputs.json').read_text());M=json.loads((P/'sources/SOURCE-MANIFEST.json').read_text());pins=json.loads((Q/'external-prefix-pins.json').read_text());pm=pins['modules'];oldm=Path(pins['original_manifest']);oldr=Path(pins['typed_full_receipt']);assert sha(oldm)==pins['original_manifest_sha256'] and sha(oldr)==pins['typed_full_receipt_sha256'];sourceManifest=json.loads(oldm.read_text());receipt=json.loads(oldr.read_text());assert receipt['exit_status']==0 and receipt['input_manifest_sha256']==sha(oldm)
D['roots'].append({'name':'current_c_27','source':str(P/'sources'),'objects':str(P/'objects')});audit=[]
for n in M['topological_order']:
 assert n not in D['modules'],n
 src=P/'sources'/(r.stem(n)+'.lean');rp=P/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());ob=r.object_pins(P/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==sha(src) and rc['objects']==ob
 for dep,di in rc['key']['imports'].items():assert D['modules'][dep]['objects']==di['objects'],(n,dep)
 D['modules'][n]={'root':'current_c_27','source':str(src),'source_sha256':sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':sha(rp)}}
 D['provenance_files'][str(rp)]=sha(rp)
closure={}
def visit(n):
 if n in closure:return
 src=pm[n]['source'] if n in pm else D['modules'][n]['source'];deps=r.imports(src,True);closure[n]={'source':src,'imports':deps}
 for dep in deps:visit(dep)
visit('ExtractedPrefixTypedFull');new=set(closure)-set(D['modules']);affected={'AspisR1RecordParser.Types'}
while True:
 more={n for n,v in closure.items() if set(v['imports'])&affected}-affected
 if not more:break
 affected|=more
assert affected<=new and len(new)==92
for n,v in closure.items():
 if n in D['modules'] and n in pm:
  assert pm[n]['source_sha256']==D['modules'][n]['source_sha256'] and pm[n]['object_sha256']==D['modules'][n]['objects']['.olean']['sha256'],('overlap identity mismatch',n)
for n in sorted(new-affected):
 p=pm[n];src=Path(p['source']);ob=r.object_pins(Path(p['object']).parents[len(n.split('.'))-1],n,D['olean_header_seal']) if False else r.object_pins(Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge/objects'),n,D['olean_header_seal']);assert sha(src)==p['source_sha256'] and ob['.olean']['sha256']==p['object_sha256'];assert sourceManifest['new_sources'][r.stem(n)+'.lean']==p['source_sha256'] and sourceManifest['new_import_objects'][r.stem(n)+'.olean']==p['object_sha256'],n
 D['modules'][n]={'root':'prefix_parser_accepted','source':str(src),'source_sha256':p['source_sha256'],'imports':closure[n]['imports'],'objects':ob};audit.append({'module':n,'source_sha256':p['source_sha256'],'objects':ob,'producing_typedFull_manifest_source_and_object_pin_checked':True})
# Every non-refreshed cached module must be independent of the repaired cone.
for n,v in D['modules'].items():assert not(set(v['imports'])&affected),(n,'stale reverse importer')
mods={};normalizations=[]
for n in sorted(affected):
 p=Path(pm[n]['source']);raw=p.read_bytes();assert sha(p)==pm[n]['source_sha256'];body=raw
 if n=='AspisR1RecordParser.Types':
  s=raw.decode();name='r1_wire.Error';ctors=[('Allocation',0),('RowOrder',2),('InvalidRow',0),('Tag',1),('Length',1),('NonCanonical',2),('Boundary',1),('Terminal',0),('EqualCirclePoints',0),('TrailingBytes',0),('Public',0)];mark='@[discriminant isize]\ninductive '+name;assert s.count(mark)==1;at=s.index(mark);end=s.index('\n\n',at);before=s[at:end];assert re.findall(r'^\| (\w+)',before,re.M)==[c for c,_ in ctors]
  aux='\n\n-- Names-only expansion of the pinned Aeneas discriminant macro.\ndef '+name+'.read_discriminant (x : '+name+') : Isize :=\n  match x with\n'+''.join('  | .'+c+' _'*ar+' => '+str(i)+'#isize\n' for i,(c,ar) in enumerate(ctors))+'\ninstance _root_.AspisR1RecordParser.'+name+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+name+' Isize where\n  read_discriminant := '+name+'.read_discriminant'
  after=before.removeprefix('@[discriminant isize]\n')+aux;s=s.replace(before,after,1);assert s.replace(after,before,1)==raw.decode();s=s.replace('\nend AspisR1RecordParser','\n#print axioms r1_wire.Error.read_discriminant\nend AspisR1RecordParser');body=s.encode();normalizations=[{'declaration':name,'constructor_arities':ctors,'tags':[[c,i] for i,(c,_) in enumerate(ctors)],'before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':hashlib.sha256(after.encode()).hexdigest(),'inverse_recovers_original_before_print_command':True}]
 dest=W/'sources'/(r.stem(n)+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(body);mods[n]={'stage_as':r.stem(n)+'.lean','source_sha256':sha(dest),'imports':r.imports(dest),'source_revision':'accepted actual Prefix strict parser; names-only RecordParser Error repair on currenta2b','source':str(p),'role':'Exact minimal reverse cone of one discriminant instance naming repair','axiom_requests':len(re.findall(r'^#print axioms ',body.decode(),re.M))}
for n in ['ExtractedPrefixTypedFullCurrent','ExtractedSourceFull25Typed']:
 p=W/'sources'/(n+'.lean');mods[n]={'stage_as':n+'.lean','source_sha256':sha(p),'imports':r.imports(p),'source_revision':'currentfe80 selectedsource repin +currenta2b canonical','source':n+'.lean','role':'Actual parser strictfull25 and constructed source raw frames/901bound; no hbytes premise','axiom_requests':len(re.findall(r'^#print axioms ',p.read_text(),re.M))}
order=[];seen=set()
def sort(n):
 if n in seen:return
 for dep in mods[n]['imports']:
  if dep in mods:sort(dep)
  else:assert dep in D['modules'],(n,dep)
 seen.add(n);order.append(n)
for n in ['AspisR1RecordParser.Types','AspisR1RecordParser.Funs','ExtractedPrefixTypedFull','ExtractedPrefixTypedFullCurrent','ExtractedSourceFull25Typed']:sort(n)
assert set(order)==set(mods)
for p in [Q/'external-prefix-pins.json',oldm,oldr]:D['provenance_files'][str(p)]=sha(p)
r.dump(W/'prefix-cache-and-naming-audit.json',{'existing_current_predecessors':27,'prefix_cached_additions':len(new-affected),'fresh_repair_cone':sorted(affected),'common_object_and_source_conflicts':0,'prefix_cache_entries':audit,'naming_expansion':normalizations,'producing_full_manifest':str(oldm),'producing_full_manifest_sha256':sha(oldm),'producing_full_receipt':str(oldr),'producing_full_receipt_sha256':sha(oldr),'rule':'Every reused prefix object/source matches accepted typedFull producing manifest. Full reverse importer set of named Error instance is freshly staged. Shared canonicala2b unchanged.'})
D['provenance_files'][str(W/'prefix-cache-and-naming-audit.json')]=sha(W/'prefix-cache-and-naming-audit.json');r.dump(W/'external-inputs.json',D);r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':order,'groups':{}});print('STAGED',len(affected),'repair ancestors +2focused targets;',len(new-affected),'cached modules appended; no compiler')
