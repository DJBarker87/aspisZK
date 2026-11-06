"""Keep native harness source as patches; materialize only inside owned scratch."""
from pathlib import Path
E=Path(__file__).resolve().parent
def read_patch(stem):
 text=(E/(stem+'.patch')).read_text()
 return ''.join(l[1:] for l in text.splitlines(True) if l.startswith('+') and not l.startswith('+++'))
def write_patch(stem,text):
 (E/(stem+'.patch')).write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/'+stem+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
