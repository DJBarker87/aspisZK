import XRy_QueryLaws
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
noncomputable section
namespace XRy_QueryTransport

theorem bind_cont {A B C : Type} (f : B → C) (r : Result A)
 (k : A → Result B) (l : A → Result C)
 (h : ∀ a, mapR f (k a) = l a) :
 mapR f (r >>= k) = r >>= l := by
 rw [mapR_bind]
 exact congrArg (fun g => r >>= g) (funext h)

theorem raw {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (inner id ce p.1,ct p.2))
   (XRn_Join_Release.transcript.Transcript.queries (ed D) (et t) row payload) =
 AspisR1PublicPreparation.QueriesModel.queries XRy_QueryLaws.rawBoundaries D t row payload := by
 unfold XRn_Join_Release.transcript.Transcript.queries AspisR1PublicPreparation.QueriesModel.queries
 rw [←XRo_Join_TranscriptBlock.absorb]
 rw [mapR_bind,bind_map]
 congr 1
 funext absorbed
 repeat' (apply bind_cont; intro)
 trace_state

#print axioms raw
#print axioms bind_cont
end XRy_QueryTransport
