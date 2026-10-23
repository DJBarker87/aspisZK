from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'S2W_OuterErasure.lean').read_text();prefix=s[s.index('theorem erase_pure'):s.index('theorem erase_mapError')]
prefix=prefix.replace('AdapterRw.','VTop_Stages.')
out='''import VTop_Flow
set_option autoImplicit false
namespace AspisR1.VTop_Erasure
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_Flow
'''+prefix
args={'tx1':'''(semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)''','tx2_common':'''(pub proof checkpoint : Slice U8)''','tx2_authenticated':'''(pub proof checkpoint : Slice U8)'''}
for n in args:
 call='semantic pub proof split' if n=='tx1' else 'pub proof checkpoint'
 extra='' if n!='tx2_authenticated' else ', VTop_Flow.tx2_common, verifier.candidate.tx2_common'
 out+=f'''
theorem {n}_source (ops : Ops) {{Hash : Type}} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) {args[n]} (obs : Option (verifier.Phase → Result Unit)) :
    VTop_Flow.{n} (sourceEffects ops) D {call} hash obs =
      verifier.candidate.{n} ops D {call} hash obs := rfl

theorem {n}_erasure (ops : Ops) {{Hash : Type}} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) {args[n]} (obs : Option (verifier.Phase → Result Unit)) :
    erase ops (VTop_Flow.{n} traceEffects D {call} hash obs) =
      verifier.candidate.{n} ops D {call} hash obs := by
  simp only [VTop_Flow.{n}, verifier.candidate.{n}, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if{extra}]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if{extra}])
    | (apply bind_congr; intro x)
    | split
#print axioms {n}_source
#print axioms {n}_erasure
'''
out+='''#print axioms erase_pure
#print axioms erase_liftM
#print axioms erase_if
#print axioms bind_congr
end AspisR1.VTop_Erasure
'''
(L/'VTop_Erasure.lean').write_text(out)
