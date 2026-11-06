from NLF_formal import *
files={'NLF_tool_pin_host.py':(E/'NLF_tool_pin_host.py').read_text()}
r=run('NLF_L083','inspect','final-tool-identity',['python3','NLF_tool_pin_host.py'],files)
assert r['exit_status']==0
r=ssh('cat '+B+'/NLF_TOOL_PINS.json');assert r.returncode==0
(E/'NLF_TOOL_PINS.json').write_text(r.stdout)
