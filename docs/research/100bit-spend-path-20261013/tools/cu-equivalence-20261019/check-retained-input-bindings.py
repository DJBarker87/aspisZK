#!/usr/bin/env python3
"""Actual sampler/semantic source binding and focused entry-invariant receipts."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest();frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
def at(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def cut(raw,anchor):
 start=raw.index(anchor);j=raw.index(b'{',start);end=j+1;depth=1
 while depth:depth+=(raw[end]==123)-(raw[end]==125);end+=1
 return raw[start:end]
source=[]
for kit,anchor in [('canonical-sampler-input','pub fn scalar('),('canonical-inputs-input','pub fn powers<const N:usize>')]:
 pins=json.loads((tool/kit/'source-pins.json').read_text())['sources'];entry=pins[anchor];body=cut(at(frozen,entry['path']),anchor.encode());assert sha(body)==entry['sha256'];source.append(dict(path=entry['path'],function=anchor,frozen_sha256=sha(body),existing_source_pin=entry))
semanticpath='crates/aspis-r1-cost-probe/src/r1_semantic.rs';semantic=at(frozen,semanticpath)
for name in ['verify_observed','verify_finish','semantic_rounds_default']:
 path=area/'tools/finish-caller-kit/input/fragments'/(name+'.rs');fragment=path.read_bytes();body=fragment[fragment.index(b'fn '):];assert body in semantic,name
 source.append(dict(path=semanticpath,function=name,source_fragment=str(path.relative_to(repo)),body_sha256=sha(body),body_in_frozen=True,cfg='not prover; removed extraction-local attributes only, function body unchanged'))
# Reuse the existing pointwise finish theorem exactly; omit only its unrelated
# selectedAlpha array packaging/SelectorExpansion dependency.
old=(area/'lean/ActualFinishAlphaSelectedCanonical.lean').read_text();start=old.index('theorem alpha_selected_canonical_of_finish_success');end=old.index('\n/-- Canonicality for',start);old=old[start:end].strip();old=old.replace('SelectedCanonical\n','AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.SelectedCanonical\n').replace('(ToSelected (','(AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.ToSelected (')
new=(area/'lean/CuSavingsRetainedSemanticFinish.lean').read_text();start=new.index('theorem alpha_selected_canonical_of_finish_success');end=new.index('\n#print axioms',start);assert old==new[start:end].strip()
names=['retained-sampler-binding-b','retained-sampler-prepared-c','retained-sampler-inputs-b','retained-sampler-block-a','retained-sampler-semantic-copy-a','retained-semantic-round-alpha-a','retained-semantic-finish-b','retained-semantic-binding-d','retained-semantic-inputs-b','retained-preparation-inputs-b'];rows=[];objects={}
for name in names:
 rp=ev/name/'receipt.json';r=json.loads(rp.read_text());path=area/'lean'/(r['module']+'.lean');assert r['exit_status']==0 and r['source_sha256']==sha(path.read_bytes()),name
 assert r['process_swaps']==r['cgroup_swap_bytes']==0,name
 audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r['print_axioms_output']);assert audits,name
 for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound'},(name,decl,axs)
 assert 'sorryAx' not in r['print_axioms_output'];objects[r['module'].replace('/','.')]=r['object_sha256']
 rows.append(dict(module=r['module'],attempt=name,source_path=str(path.relative_to(repo)),source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt_sha256=sha(rp.read_bytes()),command=r['command'],revision=r['source_revision'],features=r['features'],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'],print_axioms_output=r['print_axioms_output'],direct_imports=r['direct_imports']))
for row in rows:
 for imp in row['direct_imports']:
  if imp['module']in objects:assert imp['sha256']==objects[imp['module']],(row['module'],imp['module'])
report=dict(status='PASS',frozen=frozen,source_bindings=source,existing_finish_theorem_body_reused_exactly=True,selected=rows,closed_entry_invariants=True,endpoint='CuSavingsRetainedPreparationInputs.preparation_inputs',scope='Successful complete source tx1_prepare, under computational record specializations to actual scalar/powers and complete verifyObserved/finish source models, derives both S2 Alpha origins, all29gamma scratch SourceValue origins, all10semantic_alpha canonical values. No external child-success/canonicality/equivalence premise. Actual source folds2 selects S2; singlefold secondalpha is recorded zero separately.',runtime_coherence='CuSavingsRetainedSamplerBlock.sameBlock chooses identical common Transcript.block for scalar and scalar_k via exact Digest/transcript copies. Remaining opaque fields are unchanged common computations with no law fields.',source_boundary='Existing audited original-source Rust→Charon→Aeneas models/runtime; coordinate-only carriers; not a new wholetransaction compiler correctness theorem.')
b=(json.dumps(report,indent=2)+'\n').encode();path=ev/'RETAINED-INPUT-BINDINGS-FINAL.json'
if a.check:assert path.read_bytes()==b
else:path.write_bytes(b)
print(json.dumps(dict(check=a.check,status='PASS',selected_targets=len(rows),coherent_selected_imports=True,no_extra_axioms=True,max_rss_kib=max(r['peak_rss_kib']for r in rows))))
