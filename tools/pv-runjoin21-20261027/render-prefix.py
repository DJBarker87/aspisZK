from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';check='--check' in sys.argv
for kind,b in [('Transfer','false'),('Withdrawal','true')]:
 low=kind.lower()
 for n in range(20):
  stem=f'PV_RunJoin_{kind}Prefix{n+1:02}21';prev='PV_RunJoin_PairModel21' if n==0 else f'PV_RunJoin_{kind}Prefix{n:02}21'
  proof=f'PV_RunJoin_PairModel21.{low}' if n==0 else prev+'.source'
  s=f'''import R1Z.{prev}
set_option autoImplicit false
noncomputable section
namespace R1Z.{stem}
open R0Z.WriterRefine PV_RunJoin_FixtureRecords PV_RunJoin_AppendNative17
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- One symbolic append step; the already certified source node is never unfolded. -/
theorem source : digK (K := M) {low}{n+1} =
    AspisR1.AppendPath.pathPrefix (base {b}) (outputPair {b}) {n+1} := by
  have h := PV_RunJoin_NodeResult21.field _ _ _
    (PV_Src_CanonicalRoots.canonical (Fin.castSucc (⟨{n},by decide⟩ : Fin 20)))
    PV_RunJoin_AppendNative17.{low}_node{n}
  change R0P.nodeCompress (digK (K := M) {low}{n})
    (digK (K := M) (PV_Src_CanonicalRoots.table.val[{n}]!)) = digK {low}{n+1} at h
  rw [PV_RunJoin_AppendShape21.empty ⟨{n},by decide⟩] at h
  rw [PV_RunJoin_AppendShape21.step_zero (base {b}) rfl (outputPair {b}) ⟨{n},by decide⟩,
    ← {proof}]
  exact h.symm
#print axioms source
end R1Z.{stem}
'''
  p=D/(stem+'.lean')
  if check:assert p.read_text()==s,p
  else:p.write_text(s)
print('40 symbolic per-level append modules '+('checked' if check else 'generated'))
