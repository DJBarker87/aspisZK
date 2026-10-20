#!/usr/bin/env python3
"""Pinned actual-source helper/caller and coherent focused evidence audit."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-cu-dots.py','extract-cu-query.py','extract-cu-prefix.py','emit-cu-query.py','emit-cu-dots.py','check-prefix-source-context.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,stdout=subprocess.DEVNULL)
selected=json.loads((tool/'prefix-candidate10-selected.json').read_text());rows=[];objects={}
for name in selected:
 receipt=ev/name/'receipt.json';r=json.loads(receipt.read_text());assert r['exit_status']==0,name
 source=area/'lean'/(r['module']+'.lean');assert sha(source.read_bytes())==r['source_sha256'],name
 assert r['process_swaps']==r['cgroup_swap_bytes']==0,name
 audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",r['print_axioms_output']);assert audits,name
 for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'},(name,decl,axs)
 assert 'sorryAx' not in r['print_axioms_output'],name
 objects[r['module'].replace('/','.')]=r['object_sha256']
 rows.append(dict(attempt=name,module=r['module'],source_path=str(source.relative_to(repo)),source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt_path=str(receipt.relative_to(repo)),receipt_sha256=sha(receipt.read_bytes()),exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'],source_revision=r['source_revision'],command=r['command'],features=r['features'],print_axioms_output=r['print_axioms_output'],direct_imports=r['direct_imports']))
for row in rows:
 for imp in row['direct_imports']:
  if imp['module'] in objects:assert imp['sha256']==objects[imp['module']],(row['module'],imp['module'])
  else:assert not imp['module'].startswith(('CuSavings','AspisR1','Canonical')),('unselected_local_import',row['module'],imp['module'])
context=json.loads((tool/'prefix-candidate10-context/source-pins.json').read_text())
raw=(tool/'cu-dots-generated/Funs.lean').read_text();decls=re.findall(r'(?m)^(?:def|abbrev)\s+([^\s(]+)',raw)
rawtypes=(tool/'cu-dots-generated/Types.lean').read_text();typedecls=re.findall(r'(?m)^(?:def|structure)\s+([^\s(]+)',rawtypes)
repins=[dict(owner='fast_dots::four_dots',side=v,source_path='crates/aspis-r1-cost-probe/src/fast_dots.rs',declarations=[x for x in typedecls+decls if x.startswith(v+'.four_dots')],scope='Exact emitted helper, closure carriers, callbacks and every generated loop/body; mechanically read from raw emission.') for v in ['old_dots','new_dots']]
report=dict(candidate=context['candidate'],parent=context['parent'],frozen=context['frozen'],whole_candidate_closed=True,status='PASS',saving_combined_cu=12364,selected_targets=rows,source_context=context,helper_theorem='AspisR1.CuSavingsPrefixCandidate10.helper_equivalence',caller_theorem='AspisR1.CuSavingsPrefixCandidate10.caller_context',library_admission='CuSavingsArrayFromFn.source_eq_build consumed explicitly by old_library_admission/new_library_admission on actual source callback bodies',shared_helpers='All nine Arithmetic operations remain identical exact source callees/carriers and are universally quantified computational functions. No operation algebra, success, canonicality or candidate-equivalence premise. Source/helper identity pinned in context audit. No new Q.raw interpreter admitted.',source_boundary='Existing Rust→Charon→Aeneas translation/runtime boundary, exact std from_fn source graph already admitted. Final caller proof is inverse-audited universal source-context substitution, not a new extraction of the entire verifier.',repin_inventory=repins,complete_generated_declaration_inventory=decls)
outputs={ev/'PREFIX-CANDIDATE10-FINAL.json':(json.dumps(report,indent=2)+'\n').encode()}
for target,b in outputs.items():
 if a.check:assert target.read_bytes()==b,target
 else:target.write_bytes(b)
print(json.dumps(dict(check=a.check,status='PASS',candidate=report['candidate'],targets=len(rows),coherent_imports=True,whole_candidate_closed=True,max_rss_kib=max(r['peak_rss_kib'] for r in rows))))
