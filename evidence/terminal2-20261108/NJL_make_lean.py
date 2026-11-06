from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);m=sys.argv[2];a=f'NJL_L{n:03}'
x=json.loads((E/'NJL_L061.json').read_text());x.update(attempt=a,module=m,sources=[m+'.lean','NJL_PREDECESSOR_EXPORT.json']);x.pop('deps_fingerprint',None)
x['command'][-1]=m+'.lean';x['command'][x['command'].index('-o')+1]='NJL_objects/'+m+'.olean';x['env']['TMPDIR']='/home/dombarker/project-offloads/codex-cx-terminal2-20261108/NJL_tmp';x['expected_time']='Focused symbolic generic lemma, no concrete recurrence normalization'
(E/(a+'.json')).write_text(json.dumps(x))
