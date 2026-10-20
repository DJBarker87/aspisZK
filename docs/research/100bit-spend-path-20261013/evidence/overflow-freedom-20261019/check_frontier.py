#!/usr/bin/env python3
"""Record absence of optimized-body declarations in the checked Lean source set."""
import hashlib,json,re,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
roots=[here.parent.parent/'lean',here.parent.parent/'lean-candidates',repo/'aeneas-verif']
patterns=[r'^def .*fast_pairing',r'^def .*fast_dots',r'^def .*weights\.Weights\.(pair|new|raw)']
files=sorted({p for root in roots for p in root.rglob('*.lean')})
inputs=[{'path':str(p.relative_to(repo)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
matches=[{'file':str(p.relative_to(repo)),'pattern':pattern} for p in files for pattern in patterns if re.search(pattern,p.read_text(),re.M)]
r={'kind':'lexical-extraction-frontier-check','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'roots':[str(p.relative_to(repo)) for p in roots],'patterns':patterns,'checked_lean_file_count':len(files),'source_index_sha256':hashlib.sha256(json.dumps(inputs,sort_keys=True).encode()).hexdigest(),'matches':matches,'status':'optimized_declarations_absent' if not matches else 'review_matches','limitation':'Lexical declaration check; no claim that source generation is impossible or that an absent function is safe.'}
(here/'extraction-frontier.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':r['status'],'checked_lean_file_count':len(files)}))
