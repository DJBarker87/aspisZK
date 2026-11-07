import NNG_StateCalls094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FlushCall094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

def output (pending : verifier.BatchedWeights) : Slice aspis_core.field.QM31 :=
 ⟨(NJJ_Flush.output (toT13 pending)).val.map (fromT1 ∘ LIBC_VStateCarriers.fromQ),
 by simpa only [List.length_map] using (NJJ_Flush.output (toT13 pending)).property⟩
def call (pending : verifier.BatchedWeights) (_ : Slice aspis_core.field.QM31) := ok (output pending)

theorem update (env : RSL.Env) (pending : verifier.BatchedWeights) (a : verifier.Accumulator) :
 toT15 {a with weights:=⟨(output pending).val,(output pending).property⟩}=
 LIBC_Finish.value (toT13 pending,toT15 a) env := by
 cases a
 unfold toT15 LIBC_Finish.value output LIBC_VStateCarriers.mapVec vec
 congr 1
 apply Subtype.ext
 simp only [List.map_map,Function.comp_def,fromT1_inverse]
#print axioms update

theorem graph (env : RSL.Env) (pending : verifier.BatchedWeights) (a : verifier.Accumulator)
 (domain : LIBC_Finish.Domain (toT13 pending,toT15 a)) :
 LIBC_Finish.child.run (toT13 pending,toT15 a) env
 (LIB_Carriers.resultObs (fun s=>toT15 {a with weights:=⟨s.val,s.property⟩}) [] (call pending a.weights.deref)) := by
 refine ⟨domain,?_⟩
 apply (LIBC_Finish.graph _ env _).mpr
 exact congrArg (fun x=>RSL.Obs.mk (RSL.Exit.ret x) []) (update env pending a)
#print axioms graph
end AspisR1.NNG_FlushCall094
