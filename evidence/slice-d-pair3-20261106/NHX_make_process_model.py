from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
path='evidence/finish-install2-20261026/FIo_014/sources/FIo_NativeFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+path],text=True)
a=s.index('def _root_.FIo_Native.weights.process_kind\n');b=s.index('/-- [aspis_r1_cost_probe::weights::process_regular_kinds]',a)
s=s[a:b];header=s[:s.index('  := do')].replace('def _root_.FIo_Native.weights.process_kind','def reference')
body=s[s.rindex('\n  else\n')+len('\n  else\n'):]
# The last top-level else is unambiguous at two spaces; nested else is indented farther.
body='\n'.join(line[4:] if line.startswith('    ') else line for line in body.splitlines())
body=body.replace('_root_.FIo_Native.weights.Weights.scalar_factor','NHI_Scalar.reference')
body=body.replace('_root_.FIo_Native.weights.push_byte_products pair f s2 n','NHM_ByteProducts.reference f s2 pair n')
out='''import NHM_ByteProducts
import NHI_Scalar
import NHM_RegularDomain
set_option autoImplicit false
noncomputable section
namespace NHX_ProcessKind
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues FIo_Native
variable [FIo_Native.Allocation]
'''+header+'  := do\n'+'\n'.join(' '+line for line in body.splitlines())+'''

theorem source (w : FIo_Native.weights.Weights) (kind : Usize) (alpha : Slice NE) (f : Slice U8)
 (folds n : Usize) (ap0 ap1 : Array NE 4#usize) (scratch : alloc.vec.Vec NQ)
 (parts : Array NE 7#usize) (s2 : w.variant=FIo_Native.transport.Variant.S2) :
 FIo_Native.weights.process_kind w kind alpha f folds n ap0 ap1 scratch parts=
 reference w kind alpha f folds n ap0 ap1 scratch parts := by
 have cmp:FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant FIo_Native.transport.Variant.D=ok false:=by
  rw [s2];rfl
 unfold FIo_Native.weights.process_kind reference
 rw [cmp]
 simp only [bind_tc_ok,NHI_Scalar.cohort,NHM_ByteProducts.cohort]
 rfl

#print axioms source
end NHX_ProcessKind
end
'''
(E/'NHX_ProcessKind.lean').write_text(out)
(E/'NHX_PROCESS_MODEL_PIN.json').write_text(json.dumps(dict(source=path,sha256=hashlib.sha256(s.encode()).hexdigest(),adaptation='Exact non-D emitted branch; scalar and byte CLOSED references substituted; full Result/scratch/parts retained; no extraction rerun'),indent=2)+'\n')
