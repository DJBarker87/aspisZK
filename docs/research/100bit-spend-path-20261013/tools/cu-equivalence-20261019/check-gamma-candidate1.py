#!/usr/bin/env python3
"""Audit the explicit source-prefix claim interpretation and consuming tx1.

No failed whole-claim Aeneas emission is admitted by this audit. The source
prefix extractor remains trusted syntax-to-model code, explicitly recorded.
"""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git','-C',str(repo),*a])
predecessors={}
for script in ['check-gamma-evidence.py','check-gamma-caller-evidence.py']:
 predecessors[script]=json.loads(subprocess.check_output([sys.executable,str(tool/script)],text=True))
subprocess.run([sys.executable,str(tool/'extract-gamma-prefix.py'),'--check'],check=True,capture_output=True)
pins=json.loads((tool/'gamma-prefix-source-pins.json').read_text());candidate=pins['candidate'];parent=pins['parent'];frozen=pins['production_revision']
assert git('rev-parse',candidate+'^').decode().strip()==parent
assert git('diff','--name-only',parent,candidate).decode().splitlines()==['crates/aspis-r1-cost-probe/src/verifier.rs']
assert git('diff',frozen,'--','crates','programs')==b''
assert pins['old_tail_tokens']==pins['new_tail_tokens'] and len(pins['new_tail_tokens'])==218
assert pins['old_tail_sha256']==pins['new_tail_sha256']
assert sha((area/'lean/CuSavingsGammaPrefixData.lean').read_bytes())==pins['lean_sha256']
selected={'CuSavingsGammaSourceBinding':'gamma-source-binding-b','CuSavingsGammaPrefixData':'gamma-prefix-data-b','CuSavingsGammaCandidate1':'gamma-candidate1-a'}
refresh_path=tool/'qualified-registration-selected.json'
if refresh_path.is_file():
 for mod,attempt in json.loads(refresh_path.read_text()).items():
  if mod in selected:selected[mod]=attempt
results={};objects={};receipts={}
for module,attempt in selected.items():
 rp=ev/attempt/'receipt.json';r=json.loads(rp.read_text());src=(area/'lean'/(module+'.lean')).read_bytes()
 assert r['exit_status']==0 and sha(src)==r['source_sha256'] and src==(ev/attempt/'source.lean').read_bytes()
 assert not re.search(rb'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit)\b',src)
 o=r['print_axioms_output'];assert 'sorryAx' not in o and 'error:' not in o
 decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",o);assert decls
 for n,axs in decls:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound'},(n,axs)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 results[module]={k:r[k] for k in ['command','features','source_revision','source_sha256','object_sha256','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','foreign_lean_jobs_at_launch','print_axioms_output']}
 results[module].update(attempt=attempt,receipt_sha256=sha(rp.read_bytes()))
 objects[module]=r['object_sha256'];receipts[module]=r
# Reused complete source preparation and tx1 objects; no unchanged recompilation.
reused={}
for audit in predecessors.values():
 for module,p in audit['targets'].items():
  rp=ev/p['attempt']/'receipt.json';r=json.loads(rp.read_text());assert sha(rp.read_bytes())==p['receipt_sha256']
  assert r['source_sha256']==sha((area/'lean'/(module+'.lean')).read_bytes()) and r['exit_status']==0
  objects[module.replace('/','.')]=r['object_sha256'];reused[module]=dict(p,object_sha256=r['object_sha256'])
for module,r in receipts.items():
 for dep in r['direct_imports']:
  if dep['module'] in objects:assert dep['sha256']==objects[dep['module']],(module,dep)
src=(area/'lean/CuSavingsGammaCandidate1.lean').read_text()
assert re.findall(r'^  (\w+) : ',src.split('class SourceTail where',1)[1].split('/--',1)[0],re.M)==['run']
assert 'letI : Boundaries := sourceBoundaries common tail' in src
assert not re.search(r'\(claim_factor\s*:',src)
# Four changed Rust owners, in the established Digest32 declaration inventory.
kit=tool/'cu-gamma-input';cp=tool/'cu-gamma-caller-input'
entries=[]
for owner,label,source_kit,decls,kind in [
 ('prepared_claim','new-claim',kit,['AspisR1CuGamma.gamma_new.prepared_claim','AspisR1CuGamma.gamma_old.prepared_claim','AspisR1.CuSavingsGammaCandidate1.sourceBoundaries','AspisR1.CuSavingsGammaCandidate1.source_claim_factor'],'source-prefix interpretation; shared complete tail, not full Aeneas helper emission'),
 ('Prepared::new','new-prepare',kit,['AspisR1CuGamma.gamma_new.Prepared.gamma_new_new','AspisR1CuGamma.gamma_old.Prepared.gamma_old_new'],'complete Aeneas source emission'),
 ('tx1_prepare','new-tx1-prepare',cp,['AspisR1CuGamma.gamma_new.tx1_prepare','AspisR1CuGamma.gamma_old.tx1_prepare'],'complete Aeneas source emission'),
 ('tx1','new-tx1',cp,['AspisR1CuGamma.gamma_new.tx1','AspisR1CuGamma.gamma_old.tx1','AspisR1.CuSavingsGammaCandidate1.source_tx1_equivalence'],'complete Aeneas source emission')]:
 data=(source_kit/'fragments'/(label+'.rs')).read_bytes()
 pm=json.loads((source_kit/'source-pins.json').read_text());sp=next(c for c in pm['cuts'] if c['label']==label)
 if owner=='tx1_prepare':
  raw=(area/'lean/AspisR1CuGammaCall/Funs.lean').read_text()+'\n'+(area/'lean/AspisR1CuGammaCall/Types.lean').read_text()
  decls+=['AspisR1CuGamma.'+n for n in re.findall(r'(?m)^(?:def|structure)\s+([A-Za-z_][A-Za-z_0-9.]*)',raw) if n.startswith(('gamma_old.tx1_prepare.','gamma_new.tx1_prepare.'))]
 entries.append(dict(actual_body_emitted=owner!='prepared_claim',classification='new-source-bound',cone='gamma-reuse-tx1',rust_owner=owner,kind='fun_decls',source_path=sp['path'],current_start_byte=sp['start_byte'],current_end_byte_exclusive=sp['end_byte_exclusive'],current_file_sha256=sp['file_sha256'],source_text_sha256=sha(data),extracted_lean_declarations=decls,statement_diff='',interpretation=kind))
(ev/'GAMMA-CANDIDATE1-DECLARATION-REPIN.json').write_text(json.dumps(dict(schema_reference='design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json',candidate=candidate,parent=parent,counts={'new-source-bound':4},declarations=entries),indent=2)+'\n')
report=dict(status='TX1_EQUIVALENCE_CHECKED_UNDER_EXPLICIT_SOURCE_PREFIX_INTERPRETATION',candidate=candidate,parent=parent,frozen_production_revision=frozen,production_source_changed=False,successes=results,reused_targets=reused,source_prefix_pins_sha256=sha((tool/'gamma-prefix-source-pins.json').read_bytes()),measured_stage1_saving_cu=[34201,34243],measured_settlement_saving_cu=0,runtime_evidence='../cu-savings-20261019/FINAL-REPORT.md',boundaries=['The source-prefix extractor is trusted syntax-to-model code. Its supported fragment is one safe immutable powers29 binding followed by an identical entire tokenized tail; gamma must be absent and g used solely by copied g[l] indexing. The Lean evaluator proves the binding law and common-tail identity.','No successful direct whole-claim Aeneas extraction is claimed. Failed producer experiments are excluded. This proof uses an explicit compositional source-prefix interpretation instead.','Safe immutable arrays are interpreted by value, as in the reference model; sufficient stack/resources and the existing runtime/standard-library interpretations remain required.','The remaining whole preparation and tx1 bodies are the actual existing emissions, instantiated with one arbitrary shared tail interpreter. No candidate-equivalence, arithmetic, canonicality or success proposition is assumed.','Selected production features pool-adapter,private-leaf-salts; internal arithmetic op counting disabled. Soundness/privacy transfer and compiled-artifact certification remain separate.'],audit=dict(command=[sys.executable,*sys.argv],source_revision=git('rev-parse','HEAD').decode().strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; exact Lean axiom outputs in successes.'))
(ev/'GAMMA-CANDIDATE1-FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],new_lean_targets=len(results),reused_targets=len(reused),candidate_equivalence_axioms=0,whole_claim_aeneas_emission=False)))
