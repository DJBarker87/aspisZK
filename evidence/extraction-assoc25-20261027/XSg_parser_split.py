from pathlib import Path
import re
E=Path(__file__).resolve().parent
old='AspisR1PrefixAggregateParser.r1_wire'
s=Path('evidence/extraction-assoc21-20261027/XSc_ParseCuts.lean').read_text().replace('import XRz_ParseFold','import XSg_ParseLiteral').replace('XSc_ParseCuts','XSg_OldCuts')
s=re.sub(r'(?<![\w.])r1_wire\.',old+'.',s)
(E/'XSg_OldCuts.lean').write_text(s)
for i in range(28):
 s=Path(f'evidence/extraction-assoc21-20261027/XSc_ParseStage{i:02d}.lean').read_text()
 s=s.replace('XSc_ParseStage','XSg_OldStage').replace('XSc_ParseCuts','XSg_OldCuts').replace('XSc_ParseResume','XSg_OldResume')
 s=s.replace('import XSg_OldResume','import XSg_OldResume')
 s=re.sub(r'(?<![\w.])r1_wire\.',old+'.',s)
 (E/f'XSg_OldStage{i:02d}.lean').write_text(s)
