import R1Z.PV_OWN_View
import Init.Data.UInt.Lemmas
set_option autoImplicit false
namespace R1Z.PV_OWN_U16
open PV_OWN_Bytes PV_OWN_View
/-- Little-endian bytes; the native ABI association is a separate obligation. -/
def encode (v : UInt16) : Bytes := fun i =>
 if i=0 then some (UInt8.ofNat (v.toNat%256)) else
 if i=1 then some (UInt8.ofNat (v.toNat/256)) else none

theorem injective (a b : UInt16) (h:∀ i, i<2 → encode a i=encode b i) : a=b := by
 have h0:=h 0 (by decide)
 have h1:=h 1 (by decide)
 simp only [encode,ite_true] at h0
 simp only [encode,show ¬(1:Nat)=0 by decide,ite_false,ite_true] at h1
 have l:=congrArg UInt8.toNat (Option.some.inj h0)
 have r:=congrArg UInt8.toNat (Option.some.inj h1)
 simp only [UInt8.toNat_ofNat'] at l r
 have aa:=a.toNat_lt_size
 have bb:=b.toNat_lt_size
 apply UInt16.toNat_inj.mp
 change a.toNat<65536 at aa
 change b.toNat<65536 at bb
 change (a.toNat%256)%256=(b.toNat%256)%256 at l
 change (a.toNat/256)%256=(b.toNat/256)%256 at r
 omega

def codec : Codec UInt16 := ⟨2,2,by decide,encode,injective⟩
#print axioms injective
end R1Z.PV_OWN_U16
