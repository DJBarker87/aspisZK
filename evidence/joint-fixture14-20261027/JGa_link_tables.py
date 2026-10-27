"""Validate the split literal link-bound certificates against the frozen native table."""
from pathlib import Path
import re,sys
assert sys.argv[1:]==['--check']
r=Path(__file__).resolve().parents[2]
pattern=r'\{\s+tag :=.*?consumer := \{.*?\}\s+\}'
actual=re.findall(pattern,(r/'lean/FIq_Native12.lean').read_text(),re.S)
assert len(actual)==136
emitted=[]
for j in range(8):
 p=r/f'lean/JGa_LinkChunk{j:02}.lean'
 s=p.read_text()
 xs=re.findall(pattern,s,re.S)
 assert xs==actual[17*j:17*(j+1)],p
 assert "repeat' constructor" in s
 assert 'scalar_tac' in s
 emitted+=xs
assert emitted==actual
print('136 unchanged native links; eight 17-link symbolic bound chunks; 0 hash blocks')
