#!/usr/bin/env python3
"""Consistency gate for an explicitly incomplete source audit, not proof credit."""
import collections,hashlib,json,lzma,pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent

def main():
 a=json.load(open(P/'NKT_AUDIT.json'));controls=json.load(open(P/'NKT_CHECKER_CONTROLS.json'));reviews=json.load(open(P/'NKT_REVIEWS.json'));roots=json.load(open(P/'NKT_ROOT_REACHABILITY.json'));impact=json.load(open(P/'NKT_ROW_IMPACT.json'));llbc=json.load(open(P/'NKT_LLBC_REVIEW.json'));prov=json.load(open(P/'NKT_EXTRACTIONS.json'))
 assert all(x['pass'] for x in controls.values())
 assert controls['batch_tree']['rust_exits']==3 and controls['batch_tree']['syntactic_none_branches']==4
 assert controls['canonical_scan']['tail_loss_hits']==controls['verify_in_place']['tail_loss_hits']==0
 assert reviews and not any(r['verdict']=='UNREVIEWED_CANDIDATE' for r in reviews)
 assert {r['definition'] for r in reviews if r['verdict']=='CONFIRMED_LOST_RESULT'}=={'verifier.candidate.batch_tree_loop.body'}
 assert len(roots)==1057 and all(r['reachable_receipts'] for r in roots)
 assert {r['root'] for r in roots if r['batch_tree_dependencies']}=={'AspisR1.NHS_CheckpointPacket.source','AspisR1.RPx_Deployed.deployed'}
 assert llbc['source_text_is_exact_frozen_substring']
 assert {196,200,203,205}<={x['source_line'] for x in llbc['return_slot_writes_after_loop']}
 assert sum(x['status']=='CLOSED' for x in impact)==553
 assert a['impact_summary']['complete_audit'] is False
 assert a['remaining_obligations'] and sum(x['origin_status']=='UNRESOLVED_TOOL_ORIGIN' for x in prov)==274
 ledger=P.parent/'ledger19-20261108/NKN_LEDGER.json.xz';assert hashlib.sha256(ledger.read_bytes()).hexdigest()==a['ledger_sha256']
 for f in P.glob('*.xz'):
  side=P/(f.name[:-3]+'.sha256')
  if side.exists():assert hashlib.sha256(lzma.decompress(f.read_bytes())).hexdigest()==side.read_text().strip().split()[0],str(f)
 files=[f for f in P.rglob('*') if f.is_file()]
 assert all(f.stat().st_size<=20_000_000 for f in files)
 assert not any('__pycache__' in f.parts for f in files)
 for item in json.load(open(P/'NKT_INPUT_PINS.json'))['files']:
  q=pathlib.Path(item['path']);assert q.stat().st_size==item['bytes'] and hashlib.sha256(q.read_bytes()).hexdigest()==item['sha256'],str(q)
 changed=subprocess.check_output(['git','diff','--name-only',a['audit_revision'],'--','crates','programs'],text=True).strip();assert not changed,changed
 assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-emission-audit-20261107'
 print(json.dumps({'status':'PASS_WITH_PROVENANCE_GAPS','complete_audit':False,'closed_rows_reviewed':553,'checked_roots':len(roots),'review_packets':len(reviews),'controls':{k:v['pass'] for k,v in controls.items()},'unresolved_tool_origins':274,'new_compiler_scopes':0,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'shipped_changes':False,'ledger_unchanged':True}))
if __name__=='__main__':main()
