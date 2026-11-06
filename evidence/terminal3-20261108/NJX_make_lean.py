from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);m=sys.argv[2];a=f'NJX_L{n:03}'
x=json.loads((E/'NJX_TEMPLATE.json').read_text());x.update(attempt=a,module=m,sources=[m+'.lean','NJX_PREDECESSOR_EXPORT.json']);x['command'][-1]=m+'.lean';x['command'][x['command'].index('-o')+1]='NJX_objects/'+m+'.olean'
B='/home/dombarker/project-offloads/codex-cx-terminal3-20261108'
p=json.loads((E/'NJX_PREDECESSOR_EXPORT.json').read_text());x['env']['LEAN_PATH']=B+'/NJX_objects:'+B+'/NJX_seed:'+p['lean_path'];x['env']['CARGO_TARGET_DIR']=B+'/NJX_target';x['env']['TMPDIR']=B+'/NJX_tmp'
(E/(a+'.json')).write_text(json.dumps(x))
