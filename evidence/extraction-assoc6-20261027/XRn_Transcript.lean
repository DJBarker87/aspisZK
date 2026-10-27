import XRk_Funs
import XRn_Carriers
open Aeneas Aeneas.Std Result
open XRn_Carriers
set_option autoImplicit false
namespace XRn_Transcript

theorem tag (v : C.V) :
 XRk_Release.transport.Variant.tag (ev v)=AspisR1PublicPreparation.transport.Variant.tag v := by
 cases v <;> rfl

theorem folds (v : C.V) :
 XRk_Release.transport.Variant.folds (ev v)=AspisR1PublicPreparation.transport.Variant.folds v := by
 cases v <;> rfl

theorem start {H : Type} (D : C.D H) (hash : H) (state : Array U8 32#usize) (v : C.V) :
 mapR ct (XRk_Release.transcript.Transcript.new (ed D) hash state (ev v))=
 AspisR1PublicPreparation.transcript.Transcript.new D hash state v := by
 unfold XRk_Release.transcript.Transcript.new AspisR1PublicPreparation.transcript.Transcript.new
 rw [tag]
 simp only [mapR,bind_assoc_eq,ed,bind_tc_ok,lift]
 congr

#print axioms tag
#print axioms folds
#print axioms start
end XRn_Transcript
