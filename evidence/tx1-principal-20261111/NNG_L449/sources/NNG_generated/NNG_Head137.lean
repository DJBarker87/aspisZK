import NNG_Occurrences137
import NNG_Output137
import NNG_DLawStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Head137
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136

theorem error (a : NNG_Data137.Args) (env : RSL.Env) (e : r1_wire.Error) :
    NNG_Output137.decode a env (.Err e)=.error (NMP_Transport.toT12 e) := by
  unfold NNG_Output137.decode NMP_ResultTransport.inner NNG_Output137.error NNG_DProjection136.output
  simp only [NNG_ProjectionFallback137.representation,NNG_Transport.fromT13_inverse]
#print axioms error

theorem mark {A B Args : Type} (decode : A → B) (env : RSL.Env) (site : String) (args : Args)
    (next : Code A) (silent : NNG_Events137.events env (.call site args (.ok ()))=[]) :
    observation decode (NNG_Events137.events env)
      (NMT_CallTree.bind (invoke site args (.ok ())) (fun _=>next)) =
      observation decode (NNG_Events137.events env) next := by
  rw [NNG_ObservationAlgebra.observation_bind]
  change NNG_ObservationAlgebra.append ⟨.ret (),NNG_Events137.events env (.call site args (.ok ()))⟩
    (fun _=>observation decode (NNG_Events137.events env) next)=_
  rw [silent]
  simp only [NNG_ObservationAlgebra.append,List.nil_append]
#print axioms mark
end AspisR1.NNG_Head137
