"""Restore own ignored source inputs from the committed additions-only patch."""
from pathlib import Path
import re
E=Path(__file__).resolve().parent
lines=(E/'NEF_REFERENCE_INPUTS.patch').read_text().splitlines(True);i=0;count=0
while i<len(lines):
 assert lines[i]=='--- /dev/null\n';i+=1
 assert lines[i].startswith('+++ b/');name=lines[i][6:].strip();i+=1
 assert re.fullmatch(r'NEF_[A-Za-z0-9_]+\.rs\.txt',name),name
 m=re.fullmatch(r'@@ -0,0 \+1,(\d+) @@\n',lines[i]);assert m;i+=1
 n=int(m[1]);buf=[]
 for _ in range(n):assert lines[i].startswith('+');buf.append(lines[i][1:]);i+=1
 (E/name).write_text(''.join(buf));count+=1
print('Restored',count,'own scratch source inputs')
