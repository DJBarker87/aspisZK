#!/usr/bin/env python3
"""X1 stage 2, item C, line-preserving form (C2): the slice patterns over the accounts in lifecycle_accounts and
close_checkpoint become a length check and two indexed borrows, on the same source lines (so later panic locations
keep their line numbers). Same length test, same error values, same account reads and writes in the same order."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
p = T / 'programs/r1-cost-probe/src/r1_pool_adapter.rs'; t = p.read_text()
E = [
 ('''    let [target, authority] = accounts else {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
''', '''    if accounts.len() != 2 { // X1: indexed form of `let [target, authority] = accounts else`
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    } let (target, authority) = (&accounts[0], &accounts[1]);
'''),
 ('''    let [checkpoint, base] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
''', '''    if accounts.len() != 2 { // X1: indexed form of `let [checkpoint, base] = accounts else`
        return Err(ProgramError::NotEnoughAccountKeys);
    } let (checkpoint, base) = (&accounts[0], &accounts[1]);
'''),
]
for old, new in E:
    assert t.count(old) == 1; t = t.replace(old, new)
p.write_text(t); print('ok')
