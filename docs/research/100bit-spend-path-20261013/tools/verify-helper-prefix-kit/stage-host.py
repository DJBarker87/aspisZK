from pathlib import Path
import json,hashlib,importlib.util,shutil,re
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-proof-20261017');P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-proof-20261016');Q=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge');W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py');spec=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
sha=r.sha;data=json.loads((P/'external-inputs.json').read_text());data['roots'].extend([{'name':'current_tx1_accepted','source':str(P/'sources'),'objects':str(P/'objects')},{'name':'prefix_parser_accepted','source':str(Q/'sources'),'objects':str(Q/'objects')}]);provenance=[]
for n in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','ExtractedPreparedModel','ExtractedTx1Model','ExtractedTx1Reachability','AspisR1PrefixAggregateParser.Types','AspisR1PrefixAggregateParser.Funs']:
 assert n not in data['modules'],n
 root=P if n.startswith(('AspisR1PublicPreparation.','Extracted')) else Q
 src=root/'sources'/f'{r.stem(n)}.lean';objs=r.object_pins(root/'objects',n,data['olean_header_seal']);deps=r.imports(src,True)
 if root==P:
  receipt=root/'successful-targets'/f'{n}.json';d=json.loads(receipt.read_text());assert d['exit_status']==0 and d['key']['source_sha256']==sha(src) and d['objects']==objs
  for dep,pin in d['key']['imports'].items():assert data['modules'][dep]['objects']==pin['objects'],(n,dep)
 else:
  phase='types-bridge-a' if n.endswith('Types') else 'funs-bridge-a';receipt=root/'runs'/phase/'receipt.json';d=json.loads(receipt.read_text());assert d['exit_status']==0 and d['source_sha256']==sha(src) and d['olean_sha256']==objs['.olean']['sha256'];im=root/f'input-manifest-{phase}.json';manifest=json.loads(im.read_text());assert d['input_manifest_sha256']==sha(im) and manifest['new_sources'][r.stem(n)+'.lean']==sha(src);
  if n.endswith('Funs'):assert manifest['new_import_objects']['AspisR1PrefixAggregateParser/Types.olean']==data['modules']['AspisR1PrefixAggregateParser.Types']['objects']['.olean']['sha256']
  provenance +=[root/f'input-manifest-{phase}.json',root/'runs'/phase/'preflight.json']
 data['modules'][n]={'root':'current_tx1_accepted' if root==P else 'prefix_parser_accepted','source':str(src),'source_sha256':sha(src),'imports':deps,'objects':objs,'build_receipt':{'path':str(receipt),'sha256':sha(receipt)}}
 provenance.append(receipt)
for p in provenance:data['provenance_files'][str(p)]=sha(p)
data['scope']+=' Appended only accepted current five-module canonical tx1 closure and two Aeneas-only raw Prefix modules; current five producing receipt import-object identities checked exactly. No old nominal reverse importer or typedFull math cache added.'
r.dump(W/'external-inputs.json',data)
mods={};order=['ExtractedPrefixParseCore','ExtractedVerifyPrefixModel','ExtractedVerifyPrefixReachability']
for n in order:
 src=W/'sources'/f'{n}.lean';mods[n]={'stage_as':n+'.lean','source_sha256':sha(src),'imports':r.imports(src),'source_revision':'fe80a544a actual prefix + canonical a2b07cd9 repinned current','source':'docs/research/100bit-spend-path-20261013/lean/bridge-verify-prefix-fe80-20261017/'+n+'.lean','role':'Actual caller prefix with checked concrete parser/public helper/begin; complete finish API explicit universal','axiom_requests':len(re.findall(r'^#print axioms ',src.read_text(),re.M))}
r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':order,'groups':{}})
print('STAGED',len(data['modules']),'external modules, new3targets no compiler')
