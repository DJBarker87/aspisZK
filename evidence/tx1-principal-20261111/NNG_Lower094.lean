import NNG_Reject094
import NNG_KGuard094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Lower094
open RSL Aeneas Aeneas.Std
abbrev Args := NNG_Input094.Args

def lower (a : Args) : Args :=
 ⟨a.public_,LIB_Carriers.bytes (LIBC_Bytes.raw a.public_bytes),
  LIB_Carriers.bytes (LIBC_Bytes.raw a.proof),(LIBC_Usize.raw a.k).val⟩

theorem extent (a : Args) (own : TX1_094.Domain LIB_Instances.VL a none a.public_) :
 (lower a).public_bytes=a.public_bytes := by
 apply LIBC_Bytes.to_native
 rw [own.2.2]
 change 1880≤Usize.max
 scalar_tac
#print axioms extent

theorem domain (a : Args) (own : TX1_094.Domain LIB_Instances.VL a none a.public_) :
 TX1_094.Domain LIB_Instances.VL (lower a) none (lower a).public_ := by
 refine ⟨rfl,own.2.1,?_⟩
 rw [extent a own]
 exact own.2.2
#print axioms domain

theorem bounded (a : Args)
 (pub : (lower a).public_bytes=a.public_bytes)
 (proof : LIB_Carriers.bytes (LIBC_Bytes.raw a.proof)=a.proof)
 (k : (LIBC_Usize.raw a.k).val=a.k) : lower a=a := by
 cases a
 unfold lower at pub ⊢
 dsimp only at pub proof k
 rw [pub,proof,k]
#print axioms bounded

/-- Total carrier lowering preserves the actual094 observation. Inputs
outside native extent reject before any differing suffix could be reached. -/
theorem observation (a : Args) (env : Env)
 (own : TX1_094.Domain LIB_Instances.VL a none a.public_) :
 NNG_ProducerFull094.producer (lower a) none env=NNG_ProducerFull094.producer a none env := by
 have ownLower := domain a own
 by_cases split : a.k=SPLIT
 · have k : (LIBC_Usize.raw a.k).val=a.k := by
    rw [split]
    change (LIBC_Usize.raw 10).val=10
    exact LIBC_Usize.raw_val 10 (by scalar_tac)
   by_cases width : a.proof.length≤Usize.max
   · exact congrArg (fun input=>NNG_ProducerFull094.producer input none env)
      (bounded a (extent a own) (LIBC_Bytes.to_native a.proof width) k)
   · have bad : a.proof.length≠57607 := by
      intro equal
      apply width
      rw [equal]
      scalar_tac
     have lowerWidth : (lower a).proof.length=0 := by
      change (LIB_Carriers.bytes (LIBC_Bytes.raw a.proof)).length=0
      unfold LIBC_Bytes.raw
      rw [dif_neg width]
      rfl
     exact (NNG_Reject094.width (lower a) env ownLower (by rw [lowerWidth];decide)).trans
      (NNG_Reject094.width a env own bad).symm
 · have lowSplit : (lower a).k≠SPLIT := by
    intro equal
    apply split
    change a.k=10
    apply (NNG_KGuard094.raw_eq_split a.k).mp
    apply UScalar.eq_of_val_eq
    exact equal
   exact (NNG_Reject094.k (lower a) env ownLower lowSplit).trans (NNG_Reject094.k a env own split).symm
#print axioms observation
end AspisR1.NNG_Lower094
