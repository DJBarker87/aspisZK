import NJE_Residue
import NJA_Pow5Cut

set_option autoImplicit false
noncomputable section
namespace NJE_Pow5Packet
open Aeneas Aeneas.Std Result
open NJA_Pow5Cut

def square (x : U32) : U32 := NJE_Residue.word (x.val*x.val)
def fourth (x : U32) : U32 := NJE_Residue.word ((square x).val*(square x).val)
def result (x : U32) : U32 := NJE_Residue.word ((fourth x).val*x.val)

def events (x : U32) (i : Fin 3) : Event :=
 if i.val=0 then ⟨0,x.val,x.val,square x⟩ else
 if i.val=1 then ⟨0,(square x).val,(square x).val,fourth x⟩ else
 ⟨0,(fourth x).val,x.val,result x⟩

theorem laws (x : U32) : CalleeLaws (events x) := by
 intro i
 fin_cases i <;> simp [events,square,fourth,result,NJE_Residue.value]

theorem native_domains (x : U32) (canonical : x.val<2147483647) : Domain x (events x) := by
 constructor
 · exact canonical
 · intro i
   fin_cases i <;> simp only [events,Fin.val_zero,Fin.val_one,Fin.isValue,ite_true,ite_false,
     show ¬(2:Nat)=0 by decide,show ¬(2:Nat)=1 by decide,show ¬(1:Nat)=0 by decide]
   all_goals exact NJE_Residue.canonical _

-- The ONLY logical hypothesis is the reviewed native caller cut, with emitted
-- replies installed at each SAME call. Child laws are proved, never assumed.
theorem TX1_307 (x : U32) (len : Nat) (out : U32)
    (cut : Cut x (events x) len out) :
    NJA_FieldLaws.pow5_ref x = ok out ∧ out.val<2147483647 ∧
    (out.val : NJA_Pow5Model.K) = R0P.poseidonPow5 (x.val : NJA_Pow5Model.K) := by
 have h := compose x (events x) len out cut (laws x)
 obtain ⟨z,hz,cz,vz⟩ := NJA_Pow5Model.reference x
 have eq : z=out := Result.ok.inj (hz.symm.trans h)
 exact ⟨h,by simpa [eq] using cz,by simpa [eq] using vz⟩

#print laws
#print axioms laws
#print native_domains
#print axioms native_domains
#print TX1_307
#print axioms TX1_307
end NJE_Pow5Packet
end
