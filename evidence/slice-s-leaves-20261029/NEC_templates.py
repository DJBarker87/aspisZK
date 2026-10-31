from pathlib import Path

def template(name):
 text=(Path(__file__).parent/'NEC_templates.patch').read_text()
 block=text.split('+++ b/'+name+'.rs\n',1)[1].split('--- /dev/null',1)[0]
 return ''.join(line[1:]+'\n' for line in block.splitlines() if line.startswith('+'))
