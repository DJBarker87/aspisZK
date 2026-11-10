"""NPH_ host read-only helper: print the signature, guards and overflow-checked bindings (binary arithmetic or shift outside lift) of FILE:DEF from the replayed L187 src tree. Textual screen used to classify item 2 bodies by pattern."""
import sys,re,pathlib,json
SRC=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/src')
AR=re.compile(r'\s(\+|-|\*|/|%|>>>|<<<)\s')
for spec in sys.argv[1:]:
  f,name=spec.split(':')
  t=(SRC/f).read_text()
  m=re.search(r'^(?:@\[[^\]]*\]\s*)?def (?:_root_\.)?'+re.escape(name)+r'\b',t,re.M)
  if not m: print('NOTFOUND',spec);continue
  e=t.find('\n/--',m.start()); e2=t.find('\ndef ',m.start()+5); ends=[x for x in (e,e2) if x>0]
  body=t[m.start():min(ends) if ends else len(t)]
  hd,_,rest=body.partition(':= do')
  print('=====',name, '| lines',body.count('\n'));print('  SIG:',' '.join(hd.split())[:400])
  for l in rest.split('\n'):
    s=l.strip()
    rhs=s.split('←',1)[1] if '←' in s else ''
    if (rhs and AR.search(rhs) and 'lift' not in rhs) or s.startswith(('if ','then','else','match','|')) and AR.search(s):
      print('   OP:',s[:150])
    elif s.startswith(('if ','match ')):
      print('   G:',s[:150])
