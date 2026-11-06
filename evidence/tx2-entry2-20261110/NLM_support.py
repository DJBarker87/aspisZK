from NLM_formal import *
import sys
which=sys.argv[2];a=sys.argv[1]
if which=='identity':
 files={'NLM_inspect_retained.py':(E/'NLM_inspect_retained.py').read_text(),
 'NLM_PREDECESSOR_TOOL_PINS.json':(E.parent/'sdk-borrow-20261109/NLF_TOOL_PINS.json').read_text(),
 'NLM_SEED.json':(E/'NLM_SEED.json').read_text()}
 cmd=['python3','NLM_inspect_retained.py']
elif which=='export':
 files={'NLM_export.py':(E/'NLM_export.py').read_text(),'NLM_MODULES.json':(E/'NLM_MODULES.json').read_text()}
 cmd=['python3','NLM_export.py']
else:raise ValueError(which)
r=run(a,'inspect',which,cmd,files);sys.exit(r['exit_status'])
