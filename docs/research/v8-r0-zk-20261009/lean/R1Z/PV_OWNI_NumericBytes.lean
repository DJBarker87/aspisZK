import R1Z.PV_OWNI_ByteWord
import R1Z.PV_OWNI_RawOps
set_option autoImplicit false
namespace R1Z.PV_OWNI_NumericBytes
open Aeneas.Std PV_OWNI_RawOps PV_OWNI_ByteWord
/-- Deployed host layout: row at byte0; c0.a,c0.b,c1.a,c1.b at8,12,16,20.
The ABI selection is compiler-cohort evidence; these are active little-endian
scalar bytes. No pointer value enters the representation. -/
def limb (q : Q) (bank : Nat) : U32 :=
 if bank=0 then q.c0.a else if bank=1 then q.c0.b else if bank=2 then q.c1.a else q.c1.b

def encode (entry : Nat × Q) : PV_OWNI_EntryBytes.Entry :=
 (fun i=>byte entry.1 i.val,fun i=>byte (limb entry.2 (i.val/4)).val (i.val%4))

theorem row (entry : Nat × Q) (i : Fin 8) :
 (encode entry).1 i=byte entry.1 i.val := rfl

theorem limb_bytes (entry : Nat × Q) (bank i : Nat) (hb:bank<4) (hi:i<4) :
 (encode entry).2 ⟨bank*4+i,by omega⟩=byte (limb entry.2 bank).val i := by
 have hd:(bank*4+i)/4=bank := by omega
 have hm:(bank*4+i)%4=i := by omega
 simp only [encode,hd,hm]

#print axioms row
#print axioms limb_bytes
end R1Z.PV_OWNI_NumericBytes
