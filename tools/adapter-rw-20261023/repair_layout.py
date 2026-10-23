"""Unclip one Aeneas pretty-printer tail at column 68; preserve all tokens."""
import re

def repair(text):
    start=text.index('                                                                    let b19 ←')
    end=text.index('                                                      |',start)
    old=text[start:end]
    lines=[];depth=68;rhs=False
    for line in old.splitlines():
        s=line.strip()
        if s=='else':
            lines.append(' '*depth+s);depth+=2;rhs=False
        elif s.startswith('let ') or s.startswith('if ') or s=='then':
            lines.append(' '*depth+s);rhs=s.startswith('let ')
        else:
            lines.append(' '*(depth+2 if rhs or s.startswith('(core.result') or s in ['solana_program_error.ProgramError.InvalidAccountData)', '())'] else depth)+s)
    new='\n'.join(lines)+'\n'
    assert re.sub(r'\s+','',old)==re.sub(r'\s+','',new)
    repaired = text[:start]+new+text[end:]
    repaired = repaired.replace('                                                                    ok\n                                                                    (core.result', '                                                                    ok\n                                                                      (core.result')
    assert re.sub(r'\s+','',text)==re.sub(r'\s+','',repaired)
    return repaired
