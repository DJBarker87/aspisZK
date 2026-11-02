"""Split the timed-out Box-byte control into exact high/low native windows."""
from NEK_common_contracts import *
# K052 was the inverted output-byte relation of NDM_K009 (not its input frame).
# Each replacement below has a distinct smaller bit observation and matched
# control. NEK_ByteWindows.quotient_remainder_ext assembles the two facts.
rp='evidence/native-front4b-20261028/NDM_K009/receipt.json'
o,p,m,req,clauses=make(rp);assert len(clauses)==2
lhs='r.checkpoint_account[record.index]';rhs='NDM_native::reference::identity_ref(authenticated.checkpoint_account[record.index])'
assert lhs in clauses[0] and rhs in clauses[0]
for i,op in enumerate([' / 16',' % 16']):
 pred=f'({lhs}{op}) == old({rhs}{op})'
 for neg in [False,True]:
  a=f'NEK_K{235+2*i+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o);attr=req+'#[cfg_attr(kani,kani::ensures(|r| '+('!('+pred+')' if neg else pred)+'))]\n'
  oo[p]=o[p].replace('fn asq8_common(',attr+'fn asq8_common(',1)
  v=publish(a,rp,oo,neg,'strict smaller high/low nibble split of the K052 output-byte relation; original names/domain/native body; exact natural assembly NEK_ByteWindows')
  if v=='OPEN':break
