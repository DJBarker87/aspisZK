"""Retain the composition memory stop and isolate its unchanged loops."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'lean/PV_B3P_P227_13.lean';s=p.read_text();parts=re.split(r'(?=^/-- \[)',s,flags=re.M);header=parts[0];bs=parts[1:];assert len(bs)==7
names=[re.search(r'^def\s+(\S+)',b,re.M)[1]for b in bs];prefix=header+''.join(bs[:6])+'\nend PV_B3P_227\n\n'+''.join('#print axioms PV_B3P_227.'+n+'\n'for n in names[:6]);(D/'lean/PV_B3P_P227_13a.lean').write_text(prefix)
(D/'p13-before-isolation-resume5.lean.txt').write_text(s)
(D/'isolate-p13-resume5.json').write_text(json.dumps(dict(failed_attempt=42086,controlled_exit=143,old_source_sha256=hashlib.sha256(s.encode()).hexdigest(),unchanged_loop_names=names[:6],loop_module_sha256=hashlib.sha256(prefix.encode()).hexdigest(),next='factor selected16 reads in owned Rust then regenerate composition'),indent=2)+'\n')
