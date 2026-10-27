import XRo_Join_Transcript
import XRo_Join_ResultPair
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
namespace XRo_Join_TranscriptBlock

theorem absorb {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR ct (XRn_Join_Release.transcript.Transcript.absorb (ed D) (et t) row payload)=
 AspisR1PublicPreparation.transcript.Transcript.absorb D t row payload := by
 unfold XRn_Join_Release.transcript.Transcript.absorb AspisR1PublicPreparation.transcript.Transcript.absorb
 simp only [mapR_bind,map_ok,et,ed]
 rfl

theorem block {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p=> (p.1,ct p.2)) (XRn_Join_Release.transcript.Transcript.block (ed D) (et t) row payload)=
 AspisR1PublicPreparation.transcript.Transcript.block D t row payload := by
 unfold XRn_Join_Release.transcript.Transcript.block AspisR1PublicPreparation.transcript.Transcript.block
 rw [←absorb]
 simp only [mapR_bind,bind_map,map_ok,ct,ed]

#print axioms absorb
#print axioms block
end XRo_Join_TranscriptBlock
