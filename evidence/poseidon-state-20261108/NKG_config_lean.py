from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n,module=sys.argv[1:];a='NKG_L'+n.zfill(3)
x=json.loads((E/'NKG_L001.json').read_text());x['attempt']=a;x['module']=module
x['sources']=['NKG_lean/'+module+'.lean'];x['upload']=x['sources'];x['command'][-1]=x['sources'][0];x['command'][x['command'].index('-o')+1]='NKG_objects/'+module+'.olean';x['expected_time']='Focused new source/frame/induction theorem elaboration, no cold dependency build';(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
