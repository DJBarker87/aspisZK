from pathlib import Path
import json,re,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
mods=['AeneasMeta.Extensions','Aeneas.Extract.Extract','Aeneas.Std.Primitives','Aeneas.Std.Core.Core','Aeneas.Std.Scalar.Core','Aeneas.Std.Array.Array','Aeneas.Std.Core.Fmt','Aeneas.Std.RawPtr','Aeneas.Std.Slice','Aeneas.Std.Core.Convert','Aeneas.Std.Array.ArraySlice','Aeneas.Std.Scalar.Notations','Aeneas.Std.Core.Discriminant','Aeneas.Std.Core.Iter','Aeneas.Std.Core.Ptr','Aeneas.Std.SliceIter','Aeneas.Std.RangeIter','Aeneas.Data.Discriminant']
pending=set(mods);order=[]
while pending:
 ready=[m for m in mods if m in pending and not(set(re.findall(r'^import (\S+)',(H/'pinned-source/backends/lean'/(m.replace('.','/')+'.lean')).read_text(),re.M))&pending)]
 assert ready,'cycle';m=ready[0];pending.remove(m);order.append(m)
(H/'pin-rebuild-order.json').write_text(json.dumps(order,indent=2))
for id,m in enumerate(order,73712):
 if (H/('pincompile-'+str(id))/'receipt/receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(H/'PV_FA_launch.py'),'pincompile',str(id),m.replace('.','/')],cwd=H)
 if r.returncode:sys.exit(r.returncode)
