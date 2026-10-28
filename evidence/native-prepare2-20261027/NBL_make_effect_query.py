from pathlib import Path
import sys
root=Path(__file__).resolve().parents[2]
base=(root/'evidence/port17release-20261024/dependency-source/S1PreparedQueryEffectsV1.lean').read_text()
mat=base[base.index('  let a := Array.repeat'):base.index('  let r ← B.decode')]
mat=mat.replace('self1.state','state0').replace('self1.hash','hash')
finish=base[base.index('  let r ← B.decode'):base.index('\nprivate theorem')]
finish=finish.replace('blocks15','blocks').replace('blocks16','advances')
s='''import NBL_CodeMonad
import NBL_CodeRunLaws
import NBA_QueryFactor
set_option autoImplicit false
namespace AspisR1.NBL_QueryEffectFactor
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode
def materialize {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (hash : H) (state0 : Array U8 32#usize) :
    Code (Array (Array U8 32#usize) 8#usize × Array (Array U8 32#usize) 8#usize) := do
'''+mat+'''  pure (blocks15,blocks16)

def finish (B : QueriesModel.Boundaries) {H : Type}
    (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (self1 : transcript.Transcript H)
    (blocks advances : Array (Array U8 32#usize) 8#usize) :
    Code (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
'''+finish+'''
def queries (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Code (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
  let after ← PreparedHashEffects.absorb effects D self row payload
  let (blocks,advances) ← materialize D after.hash after.state
  finish B D after blocks advances

theorem source (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    PreparedQueryEffects.queries effects B D self row payload=queries B D self row payload := by
  unfold PreparedQueryEffects.queries queries materialize
  apply NBL_CodeMonad.bind_same; intro after
  repeat' first
    | (apply NBL_CodeMonad.bind_same; intro x)
    | rw [NBL_CodeMonad.associative]
    | rfl

#print axioms source
end AspisR1.NBL_QueryEffectFactor
'''
p=root/'lean/NBL_QueryEffectFactor.lean'
if '--check' in sys.argv:
    assert p.read_text()==s
else: p.write_text(s)
