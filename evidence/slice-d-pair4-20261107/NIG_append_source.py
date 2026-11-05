from pathlib import Path
import sys
E=Path(__file__).resolve().parent;name=sys.argv[1];assert name.startswith('NIG_')and'/'not in name
p=E/'NIG_stages.patch';s=p.read_text();i=s.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs');head=s[:i];h=''.join(l[1:]for l in s[i:].splitlines(True)if l.startswith('+')and not l.startswith('+++'))
h+='\n'+(E/name).read_text()
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NIG_stages.rs\n@@ -0,0 +1,'+str(len(h.splitlines()))+' @@\n'+''.join('+'+l for l in h.splitlines(True)))
