from pathlib import Path
import importlib.util,json,hashlib,re,difflib,shutil
C=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-read-proof-20261018');O=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge/sources');S=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-selected-current-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-trace-proof-20261018');A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
spec=importlib.util.spec_from_file_location('r',C/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
assert not (W/'external-inputs.json').exists();W.mkdir(exist_ok=True);(W/'sources').mkdir(exist_ok=True);(W/'split-sources').mkdir(exist_ok=True);shutil.copy2(C/'runner.py',W/'runner.py')
D=json.loads((C/'external-inputs.json').read_text());D['roots'].append({'name':'source_read_current','source':str(C/'sources'),'objects':str(C/'objects')})
for n in ['ExtractedSourceSemanticSampler','ExtractedSelectedSourceRecords']:
 rp=C/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());src=C/'sources'/(n+'.lean');ob=r.object_pins(C/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==r.sha(src) and rc['objects']==ob
 D['modules'][n]={'root':'source_read_current','source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}};D['provenance_files'][str(rp)]=r.sha(rp)
# Two A leaves: compare the exact producing transitive closure to current D.
identity=lambda v:(v['source_sha256'],{s:o['sha256'] for s,o in v['objects'].items()})
flat_audits=[]
for n,attempt in [('ExtractedSourceDigestAddresses','source-address-f'),('ExtractedSourceCircleFrameBound','row25-frame-b')]:
 rp=A/'runs'/attempt/'receipt.json';rc=json.loads(rp.read_text());ip=A/'runs'/attempt/'input-manifest.json';im=json.loads(ip.read_text());assert r.sha(ip)==rc['input_manifest_sha256'];closure=im['address_leaf_current_import_closure'];checked=[]
 for dep,v in closure.items():
  assert dep in D['modules'],('missing A producing import',n,dep)
  assert identity(D['modules'][dep])==identity(v),('A producing object/source differs',n,dep)
  assert r.imports(v['source'],True)==D['modules'][dep]['imports'],('A producing actual source header differs',n,dep)
  checked.append(dep)
 src=A/'sources'/(n+'.lean');ob=r.object_pins(A/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['source_sha256']==r.sha(src) and rc['olean_sha256']==ob['.olean']['sha256']
 assert r.audits(src,(A/'runs'/attempt/'lean.log').read_text())['passed']
 for path,h in rc['runtime_sha256'].items():assert D['runtime_files'][path]==h,('A compiler runtime differs',n,path)
 root='current_a_address_'+str(len(flat_audits));D['roots'].append({'name':root,'source':str(A/'sources'),'objects':str(A/'objects')});D['modules'][n]={'root':root,'source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}};D['provenance_files'][str(rp)]=r.sha(rp);D['provenance_files'][str(ip)]=r.sha(ip);flat_audits.append({'module':n,'producing_manifest':str(ip),'checked_transitive_imports':checked,'scope':'Exact producing source/object/header identity, current compiler/runtime; no byte-only stale cache adoption.'})
# Move only the exact typed parser definition, retaining its fully qualified name.
raw=(O/'R1UnifiedSemanticRecovery.lean').read_text();start=raw.index('def typed ');end=raw.index('\ntheorem typed_before_row',start);decl=raw[start:end].rstrip()+'\n'
core='''import R1InitialWalk
import R1RawRoundDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticRecovery
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}
'''+decl+'\n#print axioms typed\nend AspisR1.UnifiedSemanticRecovery\nend\n'
(W/'split-sources/R1UnifiedSemanticRecoveryCore.lean').write_text(core);full='import R1UnifiedSemanticRecoveryCore\n'+raw[:start]+raw[end:];(W/'split-sources/R1UnifiedSemanticRecovery.lean').write_text(full)
r.dump(W/'typed-core-split-audit.json',{'original_source_sha256':r.sha(O/'R1UnifiedSemanticRecovery.lean'),'original_declaration_sha256':hashlib.sha256(decl.encode()).hexdigest(),'core_sha256':hashlib.sha256(core.encode()).hexdigest(),'companion_source_sha256':hashlib.sha256(full.encode()).hexdigest(),'fully_qualified_declaration':'AspisR1.UnifiedSemanticRecovery.typed','inverse_recovers_original':full.removeprefix('import R1UnifiedSemanticRecoveryCore\n')[:start]+decl.rstrip()+'\n'+raw[end:]==raw,'source_diff':''.join(difflib.unified_diff(raw.splitlines(True),full.splitlines(True),fromfile='original',tofile='split')),'scope':'Exact proof-only parser declaration move. Companion full security module is source-only, no formal result claim.'})
mods={};order=[]
def visit(n):
 if n in D['modules'] or n in mods:return
 p=W/'split-sources'/(r.stem(n)+'.lean')
 if not p.exists():p=W/'incoming'/(r.stem(n)+'.lean')
 if not p.exists():p=S/'split-sources'/(r.stem(n)+'.lean')
 if not p.exists():p=O/(r.stem(n)+'.lean')
 assert p.exists(),('missing source',n)
 body=p.read_text();deps=r.imports(p)
 mods[n]={'stage_as':r.stem(n)+'.lean','source_sha256':hashlib.sha256(body.encode()).hexdigest(),'imports':deps,'source':str(p),'role':'Focused existing generic source-trace/typed recovery dependency or novel source composition; printed exports audited; zero requested exports compile-only'}
 for dep in deps:visit(dep)
 dest=W/'sources'/(r.stem(n)+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(body);order.append(n)
# Source-only preflight of the genuinely needed trace/parser cone first.
for n in ['R1UnifiedSemanticRecoveryCore','R1InitialWalkTrace','TraceAppend']:visit(n)
review=[{'module':n,'lines':len((W/'sources'/mods[n]['stage_as']).read_text().splitlines()),'native_decide':bool(re.search(r'\bnative_decide\b',r.uncomment((W/'sources'/mods[n]['stage_as']).read_text()))),'certificate_or_recurrence_name':bool(re.search(r'(?i)certificate|generated|recurrence',n))} for n in order]
r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':order,'groups':{'typed-prerequisites':order}});r.dump(W/'external-inputs.json',D);r.dump(W/'typed-preflight-plan.json',{'source_revision':'a555c852664c80000942f0c911e16719a5493625','new_target_count':len(order),'topological_targets':order,'shape_review':review,'new_generic_core_first':True,'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0},'no_concrete_generated_certificate':True,'A_leaf_producing_identity_audit':flat_audits});print(json.dumps({'new_targets':order,'count':len(order),'shape_review':review}))
