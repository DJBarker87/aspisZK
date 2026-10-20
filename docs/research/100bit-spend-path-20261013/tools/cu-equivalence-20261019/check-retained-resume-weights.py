#!/usr/bin/env python3
"""Check concrete prepared inactive/Libra source composition, without a whole-bundle claim."""
from pathlib import Path
import argparse,json,hashlib,re,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for script in ['check-retained-resume-source.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,stdout=subprocess.DEVNULL)
selected={'CuSavingsRetainedResumeSource':'retained-resume-source-a','CuSavingsRetainedResumeOrigins':'retained-resume-origins-a','CuSavingsRetainedResumeCells':'retained-resume-cells-a','CuSavingsRetainedResumeBinding':'retained-resume-binding-b','CuSavingsRetainedResumeWhole':'retained-resume-whole-a','CuSavingsRetainedResumeWeights':'retained-resume-weights-b'}
records={};rows=[]
for mod,attempt in selected.items():
 p=area/'lean'/f'{mod}.lean';text=p.read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque)\s|\bsorry\b|\badmit\b',text),mod
 row=dict(module=mod,source_sha256=sha(p),declarations=re.findall(r'(?m)^(?:def|theorem|abbrev)\s+([\w.]+)',text))
 if not a.source_only:
  receipt=ev/attempt/'receipt.json';r=json.loads(receipt.read_text());assert r['exit_status']==0 and r['source_sha256']==sha(p),mod
  output=r['print_axioms_output'];assert 'sorryAx'not in output
  audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert audits,mod
  for decl,axs in audits:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'},(decl,axs)
  records[mod]=r
  row.update(receipt=str(receipt),object_sha256=r['object_sha256'],command=r['command'],source_revision=r['source_revision'],features=r['features'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],print_axioms=output)
 rows.append(row)
if not a.source_only:
 for mod,r in records.items():
  for imported in r['direct_imports']:
   if imported['module']in records:assert imported['sha256']==records[imported['module']]['object_sha256'],(mod,imported)
 result=dict(status='PASS',concrete_source_replacements=[3,14],whole_retained_bundle_closed=False,final_theorem='AspisR1.CuSavingsRetainedResumeWeights.source_context_equivalence',source_admission='Exact original complete resume caller; concrete four Reader.e source calls preserve gamma plus both alpha origins; exact ten-cell semantic Reader.k loop interpreted by narrow ordered state-threading cells model with symbolic n induction. Standard owning-array fill/handback is explicit, no direct whole-loop Aeneas claim. No canonicality or successful-child premise. Same actual extra[8,9]/powers/low builders feed both retained helpers.',remaining_context='Unchanged Weights constructor operations, owning allocation/frame semantics and enclosing finish_relation contexts remain source interpretation boundaries. This is a complete resume-prefix/deferred pair-block equation, not an assertion that all ten retained components are already instantiated together.',no_equivalence_or_child_success_or_input_canonicality_premise_on_final_theorem=True,diagnostic_resource_boundary='Inherited source/runtime admission; sufficient reference resources and profiling diagnostic erasure are separately explicit. No claim of equal out-of-resource behavior.',coherent_selected_imports=True,selected_targets=rows)
 (ev/'RETAINED-RESUME-WEIGHTS-FINAL.json').write_text(json.dumps(result,indent=2)+'\n')

print(json.dumps(dict(status='SOURCE_PASS'if a.source_only else'PASS',targets=len(rows),concrete_replacements=[3,14],whole_retained_bundle_closed=False,coherent_selected_imports=not a.source_only)))
