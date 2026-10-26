"""Reproduce or check the evidence-only filter; never writes research files."""
from pathlib import Path
import hashlib,json,difflib,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
inputs=[
 ('AspisR1RecordParser.Funs','docs/research/100bit-spend-path-20261013/evidence/lean-record-source-20261015/header-parser-f/AspisR1RecordParser/Funs.lean','f6a3d5b95b781458af5a0118b76d39a14243b77958ef86eb9e5cac50ac45a2b1'),
 ('AspisR1PrefixAggregateParser.Funs','docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean','4e04e86392953c0aabc037cff0e19630a06267c59874aeba6a6391743dee433a')]
patch='';rows=[]
for m,src,sha in inputs:
 s=(R/src).read_text();assert hashlib.sha256(s.encode()).hexdigest()==sha
 start=s.rfind('/--',0,s.index('def r1_wire.Error.Insts.CoreFmtDebug.fmt'))
 end=s.index('\n/--',s.index('def r1_wire.Error.Insts.CoreFmtDebug :'))+1
 new=s[:start]+s[end:];assert 'CoreFmtDebug' not in new
 dst=E/'DFm_regenerated'/(m.replace('.','/')+'.lean')
 if '--check' in sys.argv:assert dst.read_text()==new
 else:dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(new)
 patch+=''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+src,tofile='b/'+src,n=0))
 rows.append(dict(module=m,patch_target=src,before_sha256=sha,after_sha256=hashlib.sha256(new.encode()).hexdigest(),removed_lines=[s[:start].count('\n')+1,s[:end].count('\n')]))
if '--check' in sys.argv:assert (E/'DFm_remove-debug.patch').read_text()==patch
else:
 (E/'DFm_remove-debug.patch').write_text(patch)
 (E/'DFm_patch-targets.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Evidence filter '+('checked' if '--check' in sys.argv else 'written')+': two exact pinned inputs; research files untouched')
