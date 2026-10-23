from pathlib import Path
import re
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';s=(L/'VTop_Flow.lean').read_text();a=s.index('def tx2_common ');b=s.index('def tx2_authenticated ',a);common=s[a:b].strip();start=common.index('                let (a1, pending) := val4');end=common.index('              | core.ops.control_flow.ControlFlow.Break residual =>',start);tail=common[start:end];tail='\n'.join(l[16:] for l in tail.splitlines())
header='''import VTop_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_SecondFlow
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Flow
universe v

def tail {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
    (proof : Slice U8) (p : verifier.Prepared) (obs : Option (verifier.Phase → Result Unit))
    (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
    (state : verifier.Accumulator × verifier.BatchedWeights) : M (core.result.Result Unit verifier.Error) := do
'''
for x,y in [('val4','state'),('val1','inactive'),('i2','round0'),('i3','folded'),('i4','round1')]:tail=re.sub(r'\b'+x+r'\b',y,tail)
common=common[:start]+'                tail effects proof p obs val1 i2 i3 i4 val4\n'+common[end:];common=common.replace('def tx2_common ','def common ',1)
out=header+'\n'.join('  '+l for l in tail.splitlines())+'\n\n'+common+'''

theorem common_source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    common traceEffects D pub proof checkpoint hash obs =
      VTop_Flow.tx2_common traceEffects D pub proof checkpoint hash obs := rfl

#print axioms common_source
end AspisR1.VTop_SecondFlow
end
''';(L/'VTop_SecondFlow.lean').write_text(out)
