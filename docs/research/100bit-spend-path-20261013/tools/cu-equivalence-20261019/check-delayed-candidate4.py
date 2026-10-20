#!/usr/bin/env python3
"""Audit exact candidate-4 source, accepted Lean closure and unchanged callers."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
started=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git','-C',str(repo),*a])
candidate='d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0';parent=git('rev-parse',candidate+'^').decode().strip();frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
assert parent=='534437acc6ff60dd20a84ca1393fe8f4e09341ff'
for script in ['extract-delayed-dots.py','emit-delayed-dots.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,capture_output=True)
assert git('diff','--name-only',parent,candidate).decode().splitlines()==['crates/aspis-r1-cost-probe/src/fast_dots.rs']
assert git('diff',frozen,'--','crates','programs')==b''
kit=tool/'cu-delayed-dots-input';pins=json.loads((kit/'source-pins.json').read_text());assert pins['producing_revision']==candidate and pins['parent_revision']==parent
for n,h in pins['kit_files'].items():assert sha((kit/n).read_bytes())==h,n
for n,p in pins['sources'].items():assert (kit/n).read_bytes()==git('show',p['revision']+':'+p['path'])
for attempt in ['delayed-dots-charon-b','delayed-dots-aeneas-c']:
 r=json.loads((ev/attempt/'receipt.json').read_text());assert r['exit_status']==0
 p=json.loads((ev/(attempt+'-plan.json')).read_text());assert p['source_pins_sha256']==sha((kit/'source-pins.json').read_bytes())
provenance=json.loads((tool/'delayed-emission-provenance.json').read_text())
for n in ['Funs.lean','Types.lean','FunsExternal_Template.lean']:
 matching=[h for path,h in provenance['hashes'].items() if path.endswith('/AspisR1DelayedDots/'+n)]
 assert matching==[sha((tool/'delayed-dots-generated'/n).read_bytes())],n
# The frozen helper adds only the separately inventoried fixed-prefix conversion.
path='crates/aspis-r1-cost-probe/src/fast_dots.rs';current=git('show',frozen+':'+path)
prefix=(b'    // The dot payload is exactly this prefix; paths and salts are consumed\n'
 b'    // separately. Expose its fixed extent to remove repeated slice bounds.\n'
 b'    let q:&[u8;608]=q[..608].try_into().unwrap();\n')
assert current.count(prefix)==1 and current.replace(prefix,b'')==(kit/'new_dots.rs').read_bytes()
# Source context binding is syntactic; Lean proves universal extensional
# substitution. Do not describe these fragments as separately emitted roots.
source_path='crates/aspis-r1-cost-probe/src/verifier.rs';verifier=git('show',candidate+':'+source_path)
assert verifier==git('show',parent+':'+source_path)
def fragment(name):
 m=re.search(rb'\bfn '+name.encode()+rb'<H:Digest32>',verifier);assert m,name
 begin=m.start();op=verifier.index(b'{',m.end());depth=1;end=op+1
 while depth:
  depth+=(verifier[end:end+1]==b'{')-(verifier[end:end+1]==b'}');end+=1
 return begin,end,verifier[begin:end]
roots=['query_with_geometry','query','tx1_finish','tx1','tx2','tx2_authenticated'];contexts={}
fragment_dir=tool/'delayed-source-contexts';fragment_dir.mkdir(exist_ok=True)
for name in roots:
 begin,end,data=fragment(name);(fragment_dir/(name+'.rs')).write_bytes(data)
 contexts[name]=dict(source_path=source_path,start_byte=begin,end_byte_exclusive=end,source_text_sha256=sha(data),file_sha256=sha(verifier),kind='unchanged Rust source context; covered by universal Lean substitution, not a separately emitted entrypoint')
q=fragment('query_with_geometry')[2];call=b'crate::fast_dots::four_dots(q,g)'
assert q.count(call)==1 and verifier.count(b'crate::fast_dots::four_dots(')==1
for root in ['query','tx1_finish','tx2','tx2_authenticated']:assert b'query_with_geometry(' in fragment(root)[2]
assert b'tx1_finish(' in fragment('tx1')[2]
# Changed computation has no hashes, effects or observer operations. r0-op-count
# is disabled for the selected production feature set, as in the reference.
for name in ['new_dots.rs','old_dots.rs']:
 assert not re.search(rb'\b(?:digest|hash|mark|msg|invoke|sol_log|trace)\s*(?:::|\()', (kit/name).read_bytes()),name
selected={
 'AspisR1DelayedDots/Types':'delayed-dots-types-a',
 'AspisR1DelayedDots/FunsExternal':'delayed-dots-externals-a',
 'AspisR1DelayedDots/Funs':'delayed-dots-funs-b',
 'CuSavingsDelayedScalar':'delayed-scalar-c',
 'CuSavingsDelayedArrays':'delayed-arrays-d',
 'CuSavingsDelayedLimbLoop':'delayed-limb-loop-e',
 'CuSavingsDelayedCommon':'delayed-common-a',
 'CuSavingsDelayedIterator':'delayed-iterator-b',
 'CuSavingsDelayedBatches':'delayed-batches-d',
 'CuSavingsDelayedMaterialize':'delayed-materialize-b',
 'CuSavingsDelayedKernel':'delayed-kernel-d',
 'CuSavingsDelayedCandidate4':'delayed-candidate4-b'}
results={};objects={};receipts={}
for module,attempt in selected.items():
 rp=ev/attempt/'receipt.json';r=json.loads(rp.read_text());src=(area/'lean'/(module+'.lean')).read_bytes()
 assert r['exit_status']==0 and sha(src)==r['source_sha256'] and src==(ev/attempt/'source.lean').read_bytes(),module
 assert not re.search(rb'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit)\b',src),module
 output=r['print_axioms_output'];assert 'sorryAx' not in output and 'error:' not in output
 declarations=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert declarations,module
 allowed={'propext','Classical.choice','Quot.sound','core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter'}
 for name,axs in declarations:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<=allowed,(name,axs)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 assert not r['foreign_lean_jobs_at_launch'],(module,r['foreign_lean_jobs_at_launch'])
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']}
 results[module].update(attempt=attempt,receipt_sha256=sha(rp.read_bytes()))
for module,r in receipts.items():
 for d in r['direct_imports']:
  if d['module'] in objects:assert d['sha256']==objects[d['module']],(module,d)
# Reuse exact prior source-array admission and its checked source/object pins.
r=json.loads((ev/'cu-array-from-fn-a/receipt.json').read_text());assert r['exit_status']==0
assert sha((area/'lean/CuSavingsArrayFromFn.lean').read_bytes())==r['source_sha256']
assert [d['sha256'] for d in receipts['CuSavingsDelayedCandidate4']['direct_imports'] if d['module']=='CuSavingsArrayFromFn']==[r['object_sha256']]
# Digest32-style inventory: sole changed source owner, all emitted closures/loops.
raw=(tool/'delayed-dots-generated/Funs.lean').read_text()
names=re.findall(r'(?m)^def\s+([A-Za-z_][A-Za-z_0-9.]*)',raw)
decls=['AspisR1DelayedDots.'+n for n in names if n.startswith(('new_dots.four_dots','old_dots.four_dots'))]
data=(kit/'new_dots.rs').read_bytes();begin=data.index(b'pub fn four_dots');end=len(data.rstrip())
inv=dict(schema_reference='design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json',candidate=candidate,parent=parent,counts={'new-source-bound':1},declarations=[dict(classification='new-source-bound',cone='delayed-base-dot-production-callers',rust_owner='fast_dots::four_dots',kind='fun_decls',source_path=path,current_start_byte=begin,current_end_byte_exclusive=end,current_file_sha256=sha(data),source_text_sha256=sha(data[begin:end]),historical_llbc_source_file=path,historical_span={'beg':{'line':data[:begin].count(b'\n')+1,'col':0},'end':{'line':data[:end].count(b'\n')+1,'col':1}},extracted_lean_declarations=decls,statement_diff='',notes='Complete exact candidate and parent helper; namespace instances only. Frozen helper has separately inventoried candidate10 prefix. Remaining field/pairing operations are universal unchanged computations. Caller transfer uses unconditional function equality, with no canonical input premise.')])
(ev/'DELAYED-CANDIDATE4-DECLARATION-REPIN.json').write_text(json.dumps(inv,indent=2)+'\n')
report=dict(candidate=candidate,parent=parent,frozen_production_revision=frozen,source_revision=git('rev-parse','HEAD').decode().strip(),status='SOURCE_KERNEL_EQUIVALENCE_AND_UNCHANGED_CONTEXT_SUBSTITUTION_CHECKED',successes=results,contexts=contexts,context_binding='Sole Rust delta is fast_dots.rs. Same unchanged caller computational context on both sides; all_callers_equivalence proves arbitrary context application by function extensionality. No separate whole transaction re-extraction is claimed.',assumptions=['Existing Rust/Charon/Aeneas translation and coherent Aeneas primitive/runtime semantics, including checked arithmetic/iteration and sufficient stack/resources.','Same shared computational operations on both sides; no algebraic, success, canonicality or equivalence laws are assumed for Shared.','Disabled r0-op-count/prover diagnostics; production features pool-adapter,private-leaf-salts.','Inherited core.fmt.Formatter is a Type-valued source runtime boundary, not an added proposition.'],runtime_evidence='../cu-savings-20261019/FINAL-REPORT.md',measured_combined_saving_cu=[62101,62184],production_source_changed=False,publication_pending=True,audit=dict(command=[sys.executable,*sys.argv],features=[],source_revision=git('rev-parse','HEAD').decode().strip(),exit_status=0,wall_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; exact Lean axioms outputs included in successes.'))
(ev/'DELAYED-CANDIDATE4-FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],lean_targets=len(results),changed_owners=1,unchanged_contexts=len(contexts),new_equivalence_axioms=0)))
