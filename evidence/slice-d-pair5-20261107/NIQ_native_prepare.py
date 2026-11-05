from pathlib import Path
import hashlib,subprocess,difflib,re,json,sys
E=Path(__file__).resolve().parent
target=sys.argv[3] if len(sys.argv)>3 else ''
patch=(E/'NIQ_gap_cuts.patch').read_text();inputs=json.loads((E.parent/'slice-d-pair4-20261107/NIG_BASE_REPAIR_INPUTS.json').read_text())
for section in patch.split('--- ')[1:]:
 old,rest=section.split('\n+++ b/',1);name,body=rest.split('\n',1)
 if old=='/dev/null':inputs[name]=''.join(l[1:] for l in body.splitlines(True) if l.startswith('+'))
 else:
  original=subprocess.check_output(['git','show','4bb3b3f:'+name],text=True)
  lines=original.splitlines(True);out=[];pos=0
  for line in body.splitlines(True):
   if line.startswith('@@'):
    start=int(re.match(r'@@ -(\d+)',line).group(1))-1
    out.extend(lines[pos:start]);pos=start
   elif line.startswith(' '):
    assert lines[pos]==line[1:];out.append(lines[pos]);pos+=1
   elif line.startswith('-'):
    assert lines[pos]==line[1:];pos+=1
   elif line.startswith('+'):out.append(line[1:])
  out.extend(lines[pos:]);inputs[name]=''.join(out)
inputs['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani,feature(allocator_api))]\n'+inputs['crates/aspis-r1-cost-probe/src/lib.rs']
pins={n:hashlib.sha256(t.encode()).hexdigest()for n,t in inputs.items()}
