from pathlib import Path
import textwrap,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port8EFF_PowersTail.lean').read_text()
a=s.index('    let cf2 ←');b=s.rindex('  | core.ops.control_flow.ControlFlow.Break residual =>')
tail=textwrap.indent(textwrap.dedent(s[a:b]),'  ')
head=s[s.index('  VTop_Flow.traceEffects.op13'):a]
# The last op5 binding is moved to the named continuation cut, unchanged.
c=head.index('    let r3 ←')
prefix=head[:c]+'''    VTop_Trace.perform (.op5 D proof p folded_root 1#usize hash) >>= fun r3 =>
      afterBatch D proof obs p a i g val1 i2 i3 i4 r3
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual
'''
header='''import Port9OR_Installed
import Port9OR_Driver

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchCut
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def afterBatch {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (val1 : aspis_core.field.wide_exact.WideExact) (i2 i3 i4 : Usize)
    (r3 : core.result.Result Unit verifier.Error) : Code (core.result.Result Unit verifier.Error) := do
'''
header2='''
def beforeBatch {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) : Code (core.result.Result Unit verifier.Error) := do
'''
footer='''
theorem source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    beforeBatch D proof hash obs p a i g=Port8EFF_Control.afterPowers D proof hash obs p a i g := rfl

#print axioms source
end AspisR1.Port9OR_BatchCut
end
'''
out=header+tail+header2+prefix+footer
p=L/'Port9OR_BatchCut.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
