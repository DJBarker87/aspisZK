import R1Z.PV_OWNB_LinkUnique
import R1Z.PV_OWNB_LinkBound
import R1Z.PV_OWNB_PaddingStore
set_option autoImplicit false
namespace R1Z.PV_OWNB_LinkCodec
open PV_OWN_Link PV_OWN_Bytes PV_OWN_View PV_OWNB_Padding
 theorem injective (a b : Link) (h:∀ i, i<8 → PV_OWNB_LinkBytes.encode a i=PV_OWNB_LinkBytes.encode b i) : a=b := by
 apply PV_OWNB_LinkUnique.unique a b (PV_OWNB_LinkBytes.encode b)
 · intro i v hi
   exact (h i (PV_OWNB_LinkBound.bounded a i v hi)).symm.trans hi
 · exact PV_OWNB_Padding.refl _

def codec : Codec Link := ⟨8,2,by decide,PV_OWNB_LinkBytes.encode,injective⟩

def NativeView (c : PV_OWN_Heap.Cell) (start : Nat) (v : Link) : Prop :=
 PV_OWNB_PaddingStore.Represents (PV_OWNB_LinkBytes.encode v) 8 c start

 theorem unique (c : PV_OWN_Heap.Cell) (s : Nat) (a b : Link)
 (ha:NativeView c s a) (hb:NativeView c s b) : a=b :=
 PV_OWNB_LinkUnique.unique a b (fun i=>c.contents (s+i)) ha.2 hb.2

 theorem exact_to_native (c : PV_OWN_Heap.Cell) (s : Nat) (v : Link)
 (h:Represents codec c s v) : NativeView c s v := by
 refine ⟨h.1,?_⟩
 intro i b hi
 exact (h.2 i (PV_OWNB_LinkBound.bounded v i b hi)).trans hi

attribute [local irreducible] codec NativeView
#print axioms injective
#print axioms unique
#print axioms exact_to_native
end R1Z.PV_OWNB_LinkCodec
