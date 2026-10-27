from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';check='--check' in sys.argv
for kind,b in [('Transfer','false'),('Withdrawal','true')]:
 low=kind.lower()
 for n in range(20):
  stem=f'PV_RunJoin_{kind}Frontier{n:02}21'
  proof=f'''  change digK (K := M) (PV_RunJoin_Recorded{kind}.transition.candidate_afterstate.next_frontier.val[{n}]!) = outputPair {b}
  rw [← PV_RunJoin_PairModel21.{low}]
  funext i; fin_cases i <;> rfl''' if n==0 else f'''  change digK (K := M) (PV_RunJoin_Recorded{kind}.transition.candidate_afterstate.next_frontier.val[{n}]!) =
    AspisR1.AppendNode.frozenEmpty (⟨{n},by decide⟩ : Fin 21)
  rw [PV_RunJoin_RootModel.frozen_literal]
  funext i; fin_cases i <;> rfl'''
  s=f'''import R1Z.PV_RunJoin_PairModel21
set_option autoImplicit false
noncomputable section
namespace R1Z.{stem}
open R0Z.WriterRefine PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- Sparse zero-index frontier: {'the changed carry cell' if n==0 else 'an unchanged frozen-empty cell'}. -/
theorem source : PV_RunJoin_PublicCore21.{low}.nextFrontier ⟨{n},by decide⟩ =
    (fixturePublic {b}).nextFrontier ⟨{n},by decide⟩ := by
{proof}
#print axioms source
end R1Z.{stem}
'''
  p=D/(stem+'.lean')
  if check:assert p.read_text()==s,p
  else:p.write_text(s)
print('40 sparse frontier modules '+('checked' if check else 'generated'))
