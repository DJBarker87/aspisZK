"""In-memory tamper controls for the revised gate; no registry/workspace writes."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');script=(D/'structural-zeroize190-complete.py').read_text();rt=Path.read_text;wt=Path.write_text
cases=[
 ('omit-write','zeroize-1.9.0/src/lib.rs','volatile_write(self, Z::default());','let _ = Z::default();'),
 ('duplicate-drop-delegate','zeroize-1.9.0/src/lib.rs','self.0.zeroize();','self.0.zeroize(); self.0.zeroize();'),
 ('nomem-barrier','zeroize-1.9.0/src/barrier.rs','options(readonly, preserves_flags, nostack)','options(nomem, preserves_flags, nostack)'),
 ('nonzero-u8-default','core/src/default.rs','default_impl! { u8, 0,','default_impl! { u8, 1,'),
 ('repeat-iterator-byte','core/src/slice/iter/macros.rs','self.ptr = ptr.add(1);','self.ptr = ptr.add(0);'),
 ('shift-cast-address','core/src/ptr/non_null.rs','pointer: self.as_ptr() as *mut U','pointer: self.as_ptr().wrapping_add(1) as *mut U')]
results=[]
for name,suffix,old,new in cases:
 hits=[]
 def read(p,*a,**kw):
  s=rt(p,*a,**kw)
  if str(p).endswith(suffix):
   assert old in s,(name,'mutation not reached');hits.append(str(p));return s.replace(old,new)
  return s
 def write(p,s,*a,**kw):raise RuntimeError('Tampered gate unexpectedly reached a write')
 Path.read_text=read;Path.write_text=write
 try:exec(compile(script,str(D/'structural-zeroize190-complete.py'),'exec'),{'__name__':'__main__'})
 except AssertionError as ex:results.append(dict(control=name,status='EXPECTED_REJECTION',source_reads=hits,diagnostic=str(ex)[:800]))
 else:raise RuntimeError(name+' unexpectedly passed')
 finally:Path.read_text=rt;Path.write_text=wt
 assert hits,name
(D/'zeroize-controls.json').write_text(json.dumps(dict(script_sha256=hashlib.sha256(script.encode()).hexdigest(),controls=results,source_mutations='In memory only; native source directories never changed; these are structural tamper controls, not Kani controls or native counterexamples'),indent=2)+'\n');print(len(results),'matched source tamper controls rejected')
