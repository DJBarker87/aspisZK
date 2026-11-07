import LIB_VField
set_option autoImplicit false
noncomputable section
namespace LIB_VArray
open Aeneas Aeneas.Std LIB_VScalarCarriers
def Canonical {n : Usize} (a : Array RawQ n) : Prop := ∀ q∈a.val,CanonicalRaw q
def lift {n : Usize} (a : Array RawQ n) (h : Canonical a) : Array QM31 n :=
 ⟨a.val.attach.map (fun q => ofRaw q.val (h q.val q.property)),by simpa using a.property⟩
theorem raw_lift {n : Usize} (a : Array RawQ n) (h : Canonical a) :
 array toRaw (lift a h) = a := by
 apply Subtype.ext
 simp only [array,lift,List.map_map,Function.comp_def,toRaw_ofRaw]
 exact List.map_subtype_val_attach a.val
#print axioms raw_lift
end LIB_VArray
