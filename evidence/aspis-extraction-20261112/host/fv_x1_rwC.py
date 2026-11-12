#!/usr/bin/env python3
"""X1 stage 2, item C: the slice patterns over the accounts in close_checkpoint and lifecycle_accounts become a length
check and two indexed borrows; same length test, same error values, same account reads and writes in the same order."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
p = T / 'programs/r1-cost-probe/src/r1_pool_adapter.rs'; t = p.read_text()
E = [('''    let [target, authority] = accounts else {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
''', '''    // Indexed form of `let [target, authority] = accounts else { .. }` (the translator rejects the slice pattern).
    if accounts.len() != 2 {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    let target = &accounts[0];
    let authority = &accounts[1];
'''), ('''    let [checkpoint, base] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
''', '''    // Indexed form of `let [checkpoint, base] = accounts else { .. }` (the translator rejects the slice pattern).
    if accounts.len() != 2 {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    let checkpoint = &accounts[0];
    let base = &accounts[1];
''')]
for old, new in E:
    assert t.count(old) == 1; t = t.replace(old, new)
p.write_text(t); print('ok')
