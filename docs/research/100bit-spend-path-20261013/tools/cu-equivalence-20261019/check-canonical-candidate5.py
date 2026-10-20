#!/usr/bin/env python3
"""Audit candidate-5 source API equivalence evidence without running Lean."""
from pathlib import Path
import hashlib,json,subprocess,re,argparse
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
selected=['canonical-std-types-b','canonical-std-funs-a','canonical-types-a','canonical-externals-a','canonical-funs-a','canonical-counters-e','canonical-raw-reducer-a','canonical-reduce-e','canonical-field-a','canonical-finish-b','canonical-all-e','canonical-checked-c','canonical-push-e','canonical-invariant-a','canonical-input-types-a','canonical-input-external-a','canonical-input-funs-a','canonical-input-powers-d','canonical-input-parser-g','canonical-sampler-types-a','canonical-sampler-external-a','canonical-sampler-funs-a','canonical-sampler-proof-c','canonical-source-origins-final-a','canonical-candidate5-final-a']
selected += ['canonical-input-handback-a', 'canonical-vector-types-b', 'canonical-vector-external-b', 'canonical-vector-funs-a', 'canonical-vector-loop-final-a', 'canonical-tail-step-final-a', 'canonical-tail-loop-final-a', 'canonical-tail-final-a', 'canonical-vector-contexts-final-a']
selected += ['reader-namespaced-'+x+'-a' for x in ['types','external','funs','proof']]
selected += ['canonical-field-stream-final-'+str(i) for i in range(1,7)]
selected += ['canonical-clients-integration-'+str(i) for i in range(1,13)]
selected += ['canonical-candidate5-consumers-final-a']
for script,extra in [('extract-canonical-dots.py',[]),('emit-canonical-dots.py',[]),('extract-canonical-stdlib.py',[]),('extract-canonical-inputs.py',[]),('emit-canonical-inputs.py',[]),('extract-canonical-sampler.py',[]),('emit-canonical-sampler.py',[]),('extract-canonical-vector-callers.py',[]),('emit-canonical-vector.py',[]),('check-canonical-vector-context.py',[])]:
 subprocess.run(['python3',str(tool/script),'--check']+extra,check=True,stdout=subprocess.DEVNULL)
subprocess.run(['python3',str(tool/'check-canonical-field-stream.py')],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['python3',str(tool/'check-canonical-dot-clients.py'),'--receipt-prefix','canonical-clients-integration-'],check=True,stdout=subprocess.DEVNULL)
results=[];modules={}
for name in selected:
 d=json.loads((ev/name/'receipt.json').read_text());assert d['exit_status']==0,name
 source=area/'lean'/(d['module']+'.lean')
 if d['module']=='AspisV8R17/RawReducerNat':source=repo/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/RawReducerNat.lean'
 assert sha(source.read_bytes())==d['source_sha256'],name
 stdout=(ev/name/'stdout.log').read_text();assert 'sorryAx' not in stdout and 'Lean.ofReduceBool' not in stdout and 'Lean.trustCompiler' not in stdout,name
 assert d['print_axioms_output'],name
 audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",d['print_axioms_output']);assert audits,name
 for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(','))) <= {'propext','Classical.choice','Quot.sound','core.fmt.Formatter'},(name,decl,axs)
 assert all(x not in stdout for x in ['depends on axioms: [axiom','error:','error(']),name
 assert d['process_swaps']==0 and d['cgroup_swap_bytes']==0,name
 results.append(dict(attempt=name,module=d['module'],source_path=str(source.relative_to(repo)),source_sha256=d['source_sha256'],receipt_sha256=sha((ev/name/'receipt.json').read_bytes()),exit=d['exit_status'],wall_seconds=d['wall_seconds'],peak_rss_kib=d['peak_rss_kib'],process_swap=d['process_swaps'],cgroup_swap=d['cgroup_swap_bytes'],revision=d['source_revision'],features=d['features'],command=d['command'],object_sha256=d['object_sha256'],direct_imports=d['direct_imports'],axioms=d['print_axioms_output'],foreign_lean_jobs_at_launch=d['foreign_lean_jobs_at_launch']))
 modules[d['module'].replace('/','.')]=d
for item in results:
 for dep in item['direct_imports']:
  if dep['module'] in modules:assert dep['sha256']==modules[dep['module']]['object_sha256'],(item['attempt'],dep['module'])
candidate='e58b87665233febecc1b1a75c506eac1a8b72e00';parent=subprocess.check_output(['git','-C',str(repo),'rev-parse',candidate+'^'],text=True).strip();production='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
def at(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
path='crates/aspis-r1-cost-probe/src/fast_pairing.rs';old=at(parent,path);new=at(candidate,path);assert new==at(production,path)
changed=subprocess.check_output(['git','-C',str(repo),'diff','--name-only',parent,candidate],text=True).splitlines();assert changed==[path],changed
raw_anchor=b'fn raw(self,rhs:Self)';
def cut(raw,anchor):
 start=raw.index(anchor);body=raw.index(b'{',start);end=body+1;depth=1
 while depth:depth+=(raw[end]==123)-(raw[end]==125);end+=1
 return dict(start=start,end=end,sha256=sha(raw[start:end]))
assert cut(old,raw_anchor)['sha256']==cut(new,raw_anchor)['sha256']
callers=[]
for name in ['verifier.rs','weights.rs','fast_dots.rs']:
 raw=at(production,'crates/aspis-r1-cost-probe/src/'+name);text=raw.decode();lines=text.splitlines()
 for i,line in enumerate(lines,1):
  if re.search(r'\b(?:dot|pair|tail|high)\.push\(',line):callers.append(dict(path='crates/aspis-r1-cost-probe/src/'+name,file_sha256=sha(raw),line=i,source=line.strip()))
assert len(callers)==7,callers
wide_uses=[]
for name in ['verifier.rs','weights.rs','fast_dots.rs']:
 assert b'EbyEDot' not in at(production,'crates/aspis-r1-cost-probe/src/'+name)
# Check the complete production cost-probe source closure, not only three clients.
crate_sources=subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','--name-only',production,'crates/aspis-r1-cost-probe/src'],text=True).splitlines()
for source_path in crate_sources:
 if source_path.endswith('.rs') and source_path!=path:assert b'EbyEDot' not in at(production,source_path),source_path
repins=[
 dict(owner='canonical::Dot (layout)',declarations=['old_pairing.canonical.Dot','new_pairing.canonical.Dot'],change='Drop private count; source private/public count invariant proved.'),
 dict(owner='canonical::Q::from_wide',declarations=['new_pairing.canonical.Q.from_wide'],change='New private constructor; exact source reads eight limbs.'),
 dict(owner='canonical::Dot::new',declarations=['old_pairing.canonical.Dot.new','new_pairing.canonical.Dot.new']),
 dict(owner='canonical::Dot::push',declarations=[f'{v}_pairing.canonical.Dot.{s}' for v in ['old','new'] for s in ['push','push_loop','push_loop.body']]),
 dict(owner='EbyKDot::push',declarations=['old_pairing.EbyKDot.push','new_pairing.EbyKDot.push']),
 dict(owner='EbyKDot::finish',declarations=['old_pairing.EbyKDot.finish','new_pairing.EbyKDot.finish']),
 dict(owner='EbyEDot::push',declarations=['old_pairing.EbyEDot.push','new_pairing.EbyEDot.push'],reachability='No occurrence/callsite in any other production cost-probe src Rust file (entire crate source closure scanned). Extracted, not included in EbyK API theorem. No standalone EbyEDot public-API equivalence claim.')]
report=dict(candidate=candidate,parent=parent,production_revision=production,production_fast_pairing_sha256=sha(new),exact_candidate_parent_changed_paths=changed,raw_shared_helper_body_sha256=cut(new,raw_anchor)['sha256'],selected_targets=results,source_api_theorem='CuSavingsCanonicalCandidate5.{initialization,finalization,unchanged_context}',checked_consuming_contexts=['CuSavingsCanonicalVectorContexts.six_point_claim_context','CuSavingsCanonicalVectorContexts.four_slot_tail_context','CuSavingsCanonicalCandidate5Consumers.plain_pair_context','CuSavingsCanonicalDotPartialsCanonical.caller_context','CuSavingsCanonicalCandidate5Consumers.final_relation_context'],inverse_source_context_pins=json.loads((tool/'canonical-vector-context-audit/source-pins.json').read_text()),production_callsite_inventory=callers,declaration_repins=repins,boundary='Actual source producer/counter execution predicates; original source/compiler/standard primitive boundary (exact existing array.map implementation reused), explicit kernel-checked mutable FnMut handback transport. Actual prepared claim29 and fast_dots head+tail2 complete source loops proved and consumed by checked six-point/four-slot unchanged-context substitution, with inverse source factoring audited. Actual plain pair field-stream, shared inner16/outer4/high4 and final-relation enumerate source consumers compose under unchanged continuations, with strict decoder/finish canonicality discharged. All seven production push sites are covered. No whole-transaction extraction claim; whole candidate equivalence is source-factor composition under the inherited compiler/runtime boundary.',closed_whole_candidate=True,saving_combined_cu=[22890,22916],saving_stage1=[11273,11286],saving_settlement=[11617,11630])
b=(json.dumps(report,indent=2)+'\n').encode();target=ev/'CANONICAL-CANDIDATE5-COMPONENTS.json'
if a.check:assert target.read_bytes()==b
else:target.write_bytes(b)
print(json.dumps(dict(check=a.check,successful_targets=len(results),source_import_object_pins=True,source_api_checked=True,whole_candidate_closed=True,max_rss_kib=max(x['peak_rss_kib'] for x in results))))
