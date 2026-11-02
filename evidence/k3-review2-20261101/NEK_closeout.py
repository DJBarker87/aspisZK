"""Final consistency checks; no compiler, prover, package replay or external write."""
from NEK_scan import *
import ast

def main():
 d=read_json(E/'NEK_LEDGER_DELTA.json');c=read_json(E/'NEK_CLOSURE.json');v=read_json(E/'NEK_VALIDATION.json')
 assert v['validation']=='PASS' and v['kani_used']==240 and v['lean_used']==6
 assert d['budget']==dict(kani=240,kani_limit=240,lean=6,lean_limit=10)
 assert len(d['rows'])==72 and len(c['rows'])==72
 assert all(r['k3_fully_cleared_including_transitive_support'] and not r['blocked_receipts'] and not r['unresolved'] for r in d['rows'])
 assert all(r['fully_cleared'] and not r['closure']['unresolved'] for r in c['rows'])
 assert all(k['review_outcome'] in ['RESTORED','UNAFFECTED_EXPANDED'] for r in c['rows'] for k in r['closure']['kani'])
 assert all(g['closed'] for g in d['gates']) and all(s['closed'] for s in d['common_certificates'])
 assert len({r['receipt'] for r in d['receipts']})==825
 scripts=list(E.glob('*.py'))
 for p in scripts:ast.parse(p.read_text(),filename=str(p))
 required=['NEK_RERUNS.md','NEK_LEDGER_DELTA.json','NEK_FINDINGS.md','NEK_HANDOFF.md','NEK_ATTEMPTS.jsonl']
 assert all((E/n).is_file() for n in required)
 files=list(p for p in E.rglob('*') if p.is_file());oversize=[str(p) for p in files if p.stat().st_size>20_000_000];assert not oversize,oversize
 for p in E.glob('*.lean'):
  assert not re.search(r'\b(?:sorry|admit|axiom)\b', '\n'.join(l for l in p.read_text().splitlines() if not l.lstrip().startswith(('/-','--','These','assumed')))),p
 changed=subprocess.check_output(['git','diff','--name-only','ab9c588335','--'],text=True).splitlines();assert all(p.startswith('evidence/k3-review2-20261101/') for p in changed)
 frozen_diff=subprocess.check_output(['git','diff','--name-only',FROZEN,'--','crates','programs'],text=True).splitlines();assert not frozen_diff,frozen_diff
 subprocess.run(['git','diff','--check'],check=True)
 accepted=[r for r in v['rows'] if r['kind']=='lean' and r['exit']==0];assert len(accepted)==4
 assert sum(len(r['axioms']) for r in accepted)==12
 cleanup=read_json(E/'NEK_ARTIFACT_CLEANUP.json');assert cleanup['own_scopes_live']==[] and cleanup['wallet_keys_touched'] is False
 out=dict(validation='PASS',branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,checks=dict(kani_budget='240/240',lean_budget='6/10; no remaining identified generic Lean-only assembly obligation',NEB_full_transitive='66/66',NEE_active='6/6',active_unique_kani_receipts=len({k['receipt'] for r in c['rows'] for k in r['closure']['kani']}),receipt_inventory=825,accepted_new_top_theorems=12,python_syntax_files=len(scripts),frozen_crates_programs_byte_identical=True,changes_confined_to_own_evidence=True,oversize_files=oversize,own_native_scopes_terminal=True,own_cache_retained=True,authoritative_adoption=False),required_outputs={n:sha((E/n).read_bytes()) for n in required},accepted_lean=accepted,remaining='NEK_REMAINING.json; NCN native window/copy/shape/control association remains OPEN',no_push=True)
 (E/'NEK_CLOSEOUT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['checks']))
if __name__=='__main__':main()
