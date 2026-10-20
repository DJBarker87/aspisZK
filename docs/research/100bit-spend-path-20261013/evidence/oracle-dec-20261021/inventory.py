#!/usr/bin/env python3
"""Reproducible declaration-level textual audit, not a Lean dependency checker."""
from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=Path(__file__).resolve().parent
files={p.stem:p for p in (base/'lean').glob('*.lean') if not p.stem.startswith('OracleDecision')}
files['FS2.Verifier']=root/'docs/research/v8-fs-generic-20261006/lean/FS2/Verifier.lean'
seeds=['FS2.Verifier','OracleVerifier','OracleProgramReplay','R1FinalSoundnessBinPerQueryR19','R1FinalSoundnessBinPerQueryRWire','R1FinalSoundnessBinPerQueryR9','R1FinalSoundnessBinPerQueryDecision','R1FinalSoundnessBinPerQueryCanon','D0OpeningRecoveryObstruction','D0ErasedWordObstruction','R16CanonReduction','R16CanonRecorded']
cone=set()
def visit(m):
 if m in cone or m not in files:return
 cone.add(m)
 for line in files[m].read_text().splitlines():
  if line.startswith('import '):
   for n in line.split()[1:]:visit(n)
for s in seeds:visit(s)
patterns={'decision adapter':r'\bdecisionOnBytes\b|\bErasedPrefix\b|\bErasedMessage\b','verifier equality':r'\bverifier(?:From)?_eq\b|\bverifier_congr\b','exact evaluation':r'\b(?:FS2\.)?verifier(?:From)?_eval\b','verifier API':r'\bFS2\.verifier(?:From|_reads)?\b','compiler replay':r'\bcompiled_experiment_eval\b|\bfirstReads_eq\b|\bdecoderStarts_eq\b','recording':r'\beval_record\b|recorded_transcript_eq|\b(?:recorded|compiled)_log_length\b','budgets':r'firstReads|decoderFirstReads|AdversaryQueries|\.1\.length'}
def classification(m,d):
 if m == 'FS2.Verifier' and d in ['verifier_eval','verifierFrom_eval']:
  return 'B: sampler-only exact formula must append terminal log and evaluate terminal program'
 if m == 'LiteralLegacyVerifierTrace' and d in ['trace_eq_map','verifier_trace_canonical','restricted_trace_eq']:
  return 'C: whole-log equality/canonical-label claim breaks for arbitrary decision queries; retain sampler prefix or constrain terminal labels'
 if m == 'R19BudgetOriginalReads' and d in ['verifier_queries','verifier_reads','original_reads']:
  return 'B: add terminal issued queries/first reads; 561 alone is false for arbitrary dO'
 if (m == 'DecoderQueryAccounting' and d in ['verifier_starts_le_33','recorded_starts_le']) or (m == 'BinHonestQueryBudget' and d in ['verifier_starts','recorded_starts']):
  return 'B: add terminal decoder starts; zero starts requires a label/domain proof'
 if m.startswith('R1FinalSoundness') and d == 'final_soundness':
  return 'A conditional: generic probability/semantic composition; rethread dO and retain named premises; numerical budget/start inputs must first be reproved'
 if m == 'RawRecordedLogLengthBin' and d == 'compiled_log_length':
  return 'A: equality still appends entire verifier log, including terminal queries; does not prove the log-length envelope'
 return 'A: no purity-sensitive arithmetic/equality; unchanged mathematical fact or mechanical program-valued adapter/replay port (see study for obligations)'
rows=[];signatures=[]
for mod in sorted(cone):
 lines=files[mod].read_text().splitlines(); decl='(preamble)'; declline=1; body=[]
 for i,line in enumerate(lines,1):
  match=re.match(r'(?:(?:private|protected|noncomputable|partial)\s+)*(?:theorem|lemma|def|abbrev|structure)\s+([\w\'.]+)',line)
  if match:decl=match[1];declline=i
  if line.lstrip().startswith(('--','#print')):continue
  kinds=[k for k,p in patterns.items() if re.search(p,line)]
  if kinds:rows.append({'module':mod,'declaration':decl,'declaration_line':declline,'line':i,'kinds':kinds,'text':line.strip(),'classification':classification(mod,decl)})
 if re.search(r'Erased(?:Prefix|Message).*Bool|\(d : .*Bool', '\n'.join(lines)):
  signatures.append(mod)
report={'scope':'local imports reachable from listed roots; includes historical helper imports, includes explicit FS2.Verifier and OracleVerifier API roots; excludes other external libraries. Textual references are not semantic dependence.','seeds':seeds,'module_count':len(cone),'pure_signature_modules':signatures,'cone':sorted(cone),'hits':rows}
(ev/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
md=['# Oracle-decision declaration inventory','',report['scope'],'',f'{len(cone)} local modules in cone; {len(signatures)} modules with textual pure decision signatures; {len(rows)} matched lines.','', 'A = unchanged in substance after type port; B = count terminal queries/starts; C = existing whole-log claim fails in general. Classification is an inspection assessment, not a completed port.','', '| Module / declaration | Lines | References | Assessment |','|---|---|---|---|']
groups={}
for r in rows:groups.setdefault((r['module'],r['declaration']),[]).append(r)
for (m,d),rs in groups.items():md.append(f"| `{m}.{d}` | {', '.join(str(r['line']) for r in rs)} | {', '.join(sorted(set(k for r in rs for k in r['kinds'])))} | {classification(m,d)} |")
(ev/'inventory.md').write_text('\n'.join(md)+'\n')
print(json.dumps({'cone_modules':len(cone),'pure_signature_modules':len(signatures),'hits':len(rows),'declarations':len(groups)}))
