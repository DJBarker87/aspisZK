import re,glob,sys
F=glob.glob('../prov-p4c-20261109/PCWC_E001_emitted/raw/*/Funs.lean')[0]
T=glob.glob('../prov-p4c-20261109/PCWC_E001_emitted/raw/*/Types.lean')[0]
ft=open(F).read();tt=open(T).read()
body=ft[ft.index('/-- [aspis_s1_y1_source_20261024::read_input]'):ft.index('end AspisS1ValuesOwned')]
body=re.sub(r'(?m)^@\[rust_[a-z_]*\]\n','',body)
ct=re.search(r'(/--[^\n]*\n(?:    [^\n]*\n)*)?(?:@\[[^\n]*\]\n)?(inductive CodecError where\n(?:\|[^\n]*\n)+)',tt).group(0)
ct=re.sub(r'(?m)^@\[[^\n]*\]\n','',ct)
M='S1ValuesOwnedModelV1';NS='AspisS1ValuesOwned';FR=f'{NS}.PRVFresh_{M}_w1'
hdr=f'''-- PCWM_ w1: S1ValuesOwnedModelV1, ReconstructedSource.  The fresh text is the PCWC_E001 emission of the RECONSTRUCTED crate sources/s1_y1_v1 (original Aeneas 959659a6, Charon daad69be,
-- overflow checks ON, nightly-2026-06-01 assumed, NOT the frozen 4bb3b3f toolchain and NOT frozen source: the reference is a hand-written owned-buffer model of compact::expand_values).
-- Label: ReconstructedSource, not frozen-equal.  Statements are against the gate constants of {M}.
import Aeneas
import {M}
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace {NS}
namespace PRVFresh_{M}_w1
{ct}
{body}
end PRVFresh_{M}_w1
end {NS}

namespace PRVEq.{M}_w1
open {NS}
'''
simple=['read_input','write_output','copy_chunk_loop.body','copy_chunk_loop','copy_chunk','values_owned_reference_loop.body','values_owned_reference_loop']
th=''
for n in simple:
    th+=f'''
theorem {n} : @{FR}.{n} = @{NS}.{n} := by
  rfl
#print axioms {n}
'''
th+=f'''
/-- the local enum of the reconstructed crate maps to the frozen compact.CodecError constructor by constructor (the gate's carrier) -/
def toFrozen : {FR}.CodecError → {NS}.CodecError
  | .Length => .Length
  | .NonZeroHigh => .NonZeroHigh
  | .NonCanonical => .NonCanonical

def mapRes : core.result.Result Unit {FR}.CodecError → core.result.Result Unit {NS}.CodecError
  | .Ok u => .Ok u
  | .Err e => .Err (toFrozen e)

/-- values_owned_reference: gate = fresh with the error carrier mapped (the only function whose type mentions the local enum) -/
theorem values_owned_reference (input output : alloc.vec.Vec Std.U8) :
    ({FR}.values_owned_reference input output >>= fun x => ok (mapRes x.1, x.2.1, x.2.2)) = {NS}.values_owned_reference input output := by
  unfold {FR}.values_owned_reference {NS}.values_owned_reference
  VOR_PROOF
#print axioms values_owned_reference

end PRVEq.{M}_w1
'''
proof=sys.argv[1] if len(sys.argv)>1 else 'sorry_placeholder'
open(f'PRVEq_{M}_w1.lean','w').write((hdr+th).replace('VOR_PROOF',proof))
