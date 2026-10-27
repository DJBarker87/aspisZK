from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
s=(R/'lean/JGm_TX2_Batch.lean').read_text()
a=s.index('set_option autoImplicit false');b=s.index('theorem source {Hash')
s=s[a:b]
s=s.replace('JGm_TX2_Batch','JGu_Batch').replace('JGm_TX2_Verify','JGu_Verify').replace('JGm_TX2_Terminal','JGu_Terminal')
s=s.replace('JGc_TX2_Obstruction70.folded','JGe_View.folded')
s=s.replace('JGk_TX2_Scratch0.s00','JGu_Scratch0.s00')
for t,pre in [(0,'JGf'),(1,'JGh'),(2,'JGc')]:
 s=s.replace(f'{pre}_TX2_M{t}Root.retainedRoot',f'JGr_M{t}Root.retainedRoot')
s=s.replace('JGe_View.folded 1#usize hash','JGe_View.folded 0#usize hash')
for t in range(3):s=s.replace(f'1#usize {t}#usize',f'0#usize {t}#usize')
s='import JGu_Terminal0\nimport JGu_Terminal1\nimport JGu_Terminal2\n'+s+'end AspisR1.JGu_Batch\nend\n'
(R/'lean/JGu_Batch.lean').write_text(s)
s='''import JGu_Batch
import JGr_BatchInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_PreBatch
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition
open JGr_Geometry

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) := by
  rw [JGr_BatchInputs.batch_source p input scratch prepare]
  have run := JGu_Batch.native
    (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,digest.digest⟩ :
      AspisR1Stage2.aspis_core.digest.Digest32 Unit) ()
  change Op5T_Install.body Port4B_Install.leaves
    (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,digest.digest⟩ :
      AspisR1Stage2.aspis_core.digest.Digest32 Unit)
    JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
    JGe_View.folded 0#usize ()=ok (.Ok ()) at run
  rw [run]
  rfl
#print axioms source

theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ installed.op20 .S2=ok (.Ok initial) ∧
      installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,weights,geometry,meaning,_reach⟩ := JGr_Geometry.inhabited
  exact ⟨p,scratch,initial,pending,g,prepare,queries,init,weights,geometry,meaning,source p _ scratch prepare⟩
#print axioms inhabited
end AspisR1.JGu_PreBatch
end
'''
(R/'lean/JGu_PreBatch.lean').write_text(s)
print('Generated complete batch and same-preparation consumer drafts')
