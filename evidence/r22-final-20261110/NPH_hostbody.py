"""NPH_ host read-only helper: print the full gate body of FILE:DEF from the replayed L187 src tree (reading aid for item 2)."""
import sys,re,pathlib
SRC=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/src')
for spec in sys.argv[1:]:
  f,name=spec.split(':')
  t=(SRC/f).read_text()
  m=re.search(r'^(?:@\[[^\]]*\]\s*)?def (?:_root_\.)?'+re.escape(name)+r'\b',t,re.M)
  if not m: print('NOTFOUND',spec);continue
  e=t.find('\n/--',m.start()); e2=t.find('\ndef ',m.start()+5); ends=[x for x in (e,e2) if x>0]
  print('=====',spec);print(t[m.start():min(ends) if ends else len(t)])
