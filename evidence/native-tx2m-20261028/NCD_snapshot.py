from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NCD_[LK]*/receipt.json'))]
unknown=[a for a in ['NCD_L002','NCD_L006'] if not (E/a/'receipt.json').exists()]
negative=[r['attempt'] for r in receipts if r['kind']=='kani' and r['exit_status']!=0 and r['command'][r['command'].index('--harness')+1].endswith('copy_negative') and 'Failed Checks: assertion failed: b[15] == 0' in (E/r['attempt']/'stdout.log').read_text()]
summary=dict(conservative_config_slots={k:sum(bool(re.fullmatch('NCD_'+prefix+r'[0-9]+\.json',p.name)) for p in E.iterdir()) for k,prefix in [('lean','L'),('kani','K')]},intended_negative_controls=negative,inherited=dict(lean=20,kani=55),current=dict(lean=len([r for r in receipts if r['kind']=='lean'])+len(unknown),kani=len([r for r in receipts if r['kind']=='kani'])),ceilings=dict(lean=120,kani=50),unresolved_reserved=unknown,receipt_count=len(receipts),passes=[r['attempt'] for r in receipts if r['exit_status']==0],failures=[dict(attempt=r['attempt'],module=r.get('module'),exit=r['exit_status']) for r in receipts if r['exit_status']!=0 and r['attempt'] not in negative],receipt_hashes={str(p.relative_to(E)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(E.glob('NCD_[LK]*/receipt.json'))})
(E/'NCD_COUNTS.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary['current']))
