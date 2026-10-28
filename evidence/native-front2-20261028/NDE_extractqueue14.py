from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,root in [(14,'interpolation_limb_ref'),(15,'residual_ref'),(16,'equality_ref'),(17,'tag_step_ref'),(18,'active_step_ref'),(19,'pattern_step_ref'),(20,'fields_word_ref')]:
 p=E/'NDE_extract.py';s=p.read_text();import re
 s=re.sub(r"roots=\[[^\n]*", "roots=['crate::"+root+"']",s)
 s=re.sub(r"namespace='[^']*'", "namespace='NDE_Reference"+str(n)+"'",s)
 s=re.sub(r"dest=B/'[^']*'", "dest=B/'NDE_extracted"+str(n)+"'",s);p.write_text(s)
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_E{n:03}','extract',root])
 if r.returncode:raise SystemExit(r.returncode)
