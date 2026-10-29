"""Fail-closed own-1 association of the exact deployed shared-return match.
No arithmetic, hidden callee, mutable loan, store or cleanup is elided.
"""
from pathlib import Path
import json,hashlib,re
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';inv=json.loads((D/'resume9/body-inventory.json').read_text())
f=next(f for f in inv['files']if f['family']=='terminal')
for k in ['source','owned']:
 p=Path(f[k]);assert hashlib.sha256(p.read_bytes()).hexdigest()==f[k+'_sha256']
source_text=Path(f['source']).read_text();assert '#[derive(Clone, Copy)]\n    pub enum Public' in source_text
r=next(r for r in inv['bodies']if r['family']=='terminal' and r['key']=='transition#0')
assert r['status']=='identical' and r['source']['tokens']==r['owned']['tokens']
tokens=r['source']['tokens'];a=tokens.index('{');body=tokens[a:]
expected=['{','match','self','{','Self',':',':','Transfer','(','_',',','t',')','|','Self',':',':','Withdrawal','(','_',',','t',')','=','>','t','}','}']
assert body==expected,body
row=dict(body='r0.Public.transition',rule='own-1 structural shared-loan binding',source=f['source'],owned=f['owned'],source_file_sha256=f['source_sha256'],owned_file_sha256=f['owned_sha256'],source_span=[r['source']['line'],r['source']['end_line']],owned_span=[r['owned']['line'],r['owned']['end_line']],token_sha256=r['source']['sha256'],checked_every_body_token=True,steps=[dict(source='consume Copy Public discriminant; Transfer(_,t) arm',model='BorrowedPublic14.Transfer p t / transition_transfer_identity14; returns exactly same identity and value'),dict(source='Withdrawal(_,t) arm in same or-pattern',model='BorrowedPublic14.Withdrawal p t / transition_withdrawal_identity14; returns exactly same identity and value'),dict(source='shared reference return; no dereference, allocation or mutation',model='Shared14 identity retained; transition_loan_continuation14 permits identity-sensitive continuations'),dict(source='caller reads immutable value',model='transition_loan_binding14 transports to transition_source13 after value erasure')],callees=[],stores=[],drop_glue='Public is Copy; fields are shared references. No destructor or explicit Drop in this body. No cleanup side effects.',error_abort_divergence='exhaustive two-arm pure return; no failure operation',lean_module='PV_B3P_TransitionLoan14227',status='Exact source statement map checked; loan/continuation laws compiled at 69462. No std/dependency callees in this body; source-to-machine remains at V370.',compiler_boundary='source-to-machine V370 / pending owner D381,D386 retained; never T')
(O/'transition-native-association.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(dict(exact_body_checked=True,statements=2,callees=0)))
