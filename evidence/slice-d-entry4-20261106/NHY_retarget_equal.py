from pathlib import Path
import hashlib,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];rows=[]
for old,new in [('NCV_EqualStep','NHY_EqualStep'),('NCV_EqualRun','NHY_EqualRun'),('NCV_EqualValue','NHY_EqualValue')]:
 p=R/'lean'/(old+'.lean');src=p.read_text();s=src
 for a,b in [('NCV_EqualStep','NHY_EqualStep'),('NCV_EqualRun','NHY_EqualRun'),('NCV_EqualValue','NHY_EqualValue'),('NCV_ZeroStep','NHY_ZeroStep'),('NCV_Loop','NHY_ZeroLoop'),('NCV_Reference','NCX_Reference')]:s=s.replace(a,b)
 (E/(new+'.lean')).write_text(s);diff=''.join(difflib.unified_diff(src.splitlines(True),s.splitlines(True),fromfile=str(p.relative_to(R)),tofile=new+'.lean'));(E/(new+'.diff')).write_text(diff)
 rows.append(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(src.encode()).hexdigest(),destination=new+'.lean',destination_sha256=hashlib.sha256(s.encode()).hexdigest(),edits='namespace/import/emitted-body owner retargets only; mathematical proof bodies retained',diff=new+'.diff'))
(E/'NHY_EQUAL_RETARGET.json').write_text(json.dumps(rows,indent=1)+'\n')
