from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parents[2]
ev=Path(__file__).resolve().parent
src=base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=src.read_text()
def item(name):
 a=s.index('def '+name+'\n'); z=s.index('\n/--',a)
 return s[a:z].rstrip()+'\n'
root=item('multiproof.root_matches')
index=item('multiproof.index_at')
body=item('multiproof.verify_in_place_loop0.body')
body=body.replace('def multiproof.verify_in_place_loop0.body','def terminalBody').replace('  {H : Type}', '  (ops : TerminalOps)\n  {H : Type}')
old='multiproof.verify_in_place_loop0_loop0 aspis_coredigestDigest32Inst hash'
assert body.count(old)==1
body=body.replace(old,'ops.level')
header='''import R13WireToBin
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13SourceTerminal
open AspisR1Stage2
abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
/-- Only the inner level loop is parameterized. It is NOT assumed correct. -/
structure TerminalOps where
  level : multiproof.Arity → Indices → Values → Usize → Slice U8 → Usize → Usize → Usize → Option Bool →
    Result (multiproof.Arity × Indices × Values × Usize × Usize × Option Bool × U32)
'''
# Local helper names differ by namespace only; retain their exact bodies.
text=header+root+index+'\n'+body+'\nend AspisR1Stage2.R13SourceTerminal\n'
p=base/'lean/R13SourceTerminalBody.lean'
if not p.exists():p.write_text(text)
assert p.read_text()==text
(ev/'terminal-binding.json').write_text(json.dumps(dict(source=str(src.relative_to(base)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),adapter_sha256=hashlib.sha256(text.encode()).hexdigest(),exact_except=['namespace','terminalBody name','TerminalOps argument','inner level-loop call replaced by ops.level'],whole_outer_loop_body=True,claim='Only the exhausted-range branch is proved by R13SourceTerminal; successful whole-loop reachability remains open'),indent=2)+'\n')
