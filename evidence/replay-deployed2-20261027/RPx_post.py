import json,sys
from RPx_attempt import E,run
p=json.loads((E/'RPx_plan.json').read_text())
if __name__=='__main__':
 rs=[json.loads(f.read_text()) for f in E.glob('RPx_*/receipt.json')]
 module=sys.argv[1];file=E/(module+'.lean');imports=['Init']+[l.split()[1] for l in file.read_text().splitlines() if l.startswith('import ')]
 assert not any(d['module']==module for d in rs),'unchanged audit already attempted'
 assert len(rs)<150
 d=run(f'RPx_{len(rs)+1:04d}',module,file,imports);assert d['exit_status']==0,d
