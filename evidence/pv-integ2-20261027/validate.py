"""Receipt validation only; never reruns a proof or native gate."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];standard={'propext','Classical.choice','Quot.sound'}
merges=[json.loads(x) for x in (E/'merges.jsonl').read_text().splitlines()];assert len(merges)==9 and all(x['exit']==0 for x in merges)
elf=json.loads((E/'elf-gate.json').read_text());assert elf['passed'] and len(elf['builds'])==3
for b in elf['builds']:
 assert b['matches'] and b['sha256']==b['expected'] and b['receipt']['exit_status']==0
 assert b['receipt']['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and b['receipt']['swaps']==0
receipts=[]
for p in sorted((E/'lean-receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());assert r['exit']==0 and r['swap']=='0';assert r['source_sha256']==hashlib.sha256((p.parent/'source.lean.txt').read_bytes()).hexdigest()
 assert r['peak_RSS_KiB'] is not None and r['wall'] is not None
 text=(p.parent/'out.log').read_text();matches=re.findall(r"'([^'\n]+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
 bad=[]
 for n,kind,raw in matches:
  a={x.strip() for x in raw.split(',') if x.strip()}
  if a-standard:bad.append(dict(theorem=n,unsupported=sorted(a-standard)))
 assert not bad,(p,bad)
 assert len(matches)==len(r['axioms']),(p,len(matches),len(r['axioms']))
 r['axiom_report_count']=len(matches);receipts.append(r)
assert len(receipts)==26
final=next(x for x in receipts if x['attempt']==54597);plan=json.loads((E/'formal-plan.json').read_text());out=(E/'lean-receipts/54597/out.log').read_text();reported=set(re.findall(r"'([^'\n]+)' (?:depends on axioms|does not depend on any axioms)",out));assert set(plan['audit_targets'])==reported,(set(plan['audit_targets'])-reported,reported-set(plan['audit_targets']))
assert final['axiom_report_count']==533
assert not json.loads((E/'static-proof-check.json').read_text())['forbidden_declarations_or_terms']
assert not subprocess.check_output(['git','diff','5465d05960f6433ec1b465037f36829cb58dec8f','HEAD','--','crates','programs','tools','scripts','docs','AspisFormal'],cwd=R,text=True)
summary=dict(lean_attempts=26,lean_budget=100,kani_attempts=0,kani_budget=0,all_successful=True,combined_audit={k:final[k] for k in ['attempt','module','exit','wall','peak_RSS_KiB','swap','source_revision','source_sha256','deps_fingerprint','axiom_report_count']},axioms_allowed=sorted(standard),unsupported_axioms=[],endpoint_premises_removed=0,target_established=False,receipts=receipts)
(E/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: nine clean merges, three ELF pins, 25 missing-object rechecks, 533 combined axiom reports; standard axioms only')
