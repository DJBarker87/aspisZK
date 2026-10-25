from pathlib import Path
import textwrap,sys
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'VTop_Flow.lean').read_text();s=s[s.index('def tx1'):s.index('\ndef tx2_common')]
b=s[s.index('  := do')+len('  := do'):].strip('\n').replace('effects.','VTop_Flow.traceEffects.')
a=b.index('            let r5 ←'); cut=b.index('            let cf4 ←',a); end=b.index('\n          | core.ops.control_flow.ControlFlow.Break residual =>',cut)+1
tail=textwrap.indent(textwrap.dedent(b[cut:end]),'  ')
prefix=b[:a]+'''            VTop_Trace.perform (.op5 aspis_coredigestDigest32Inst proof val folded_root 0#usize hash) >>= fun r5 =>
              afterBatch aspis_coredigestDigest32Inst public_bytes proof k hash obs val val1 g1 r5
'''+b[end:]
header='''import Port9OR_FirstBatch

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_TX1Cut
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def afterBatch {Hash : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (val : verifier.Prepared) (val1 : verifier.Accumulator)
    (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (r5 : core.result.Result Unit verifier.Error) : Code (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
'''
header2='''
def code {Hash : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit)) : Code (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
'''
footer='''
theorem source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit)) :
    code D public1 public_bytes proof k hash obs=VTop_Flow.tx1 VTop_Flow.traceEffects D public1 public_bytes proof k hash obs := rfl

#print axioms source
end AspisR1.Port10AUTH_TX1Cut
end
'''
out=header+tail+header2+prefix+footer;p=L/'Port10AUTH_TX1Cut.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
