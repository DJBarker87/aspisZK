import NFS_AccumPart01
import NFP_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_ReadCanonical
open Aeneas Aeneas.Std Result
open Port3_PushFrame (bind_success)
abbrev Native := FIo_Native.aspis_core.field.wide_exact.WideExact

theorem limbs (xs : Array U32 8#usize) (out : Native)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs xs=ok (some out)) :
 NFN_LPi_FieldValues.canonE out := by
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
 obtain ⟨w0,hw0,run⟩ := bind_success _ _ _ run
 split at run
 · cases run
 · rename_i bound0
   obtain ⟨w1,hw1,run⟩ := bind_success _ _ _ run
   split at run
   · cases run
   · rename_i bound1
     obtain ⟨w2,hw2,run⟩ := bind_success _ _ _ run
     split at run
     · cases run
     · rename_i bound2
       obtain ⟨w3,hw3,run⟩ := bind_success _ _ _ run
       split at run
       · cases run
       · rename_i bound3
         obtain ⟨w4,hw4,run⟩ := bind_success _ _ _ run
         split at run
         · cases run
         · rename_i bound4
           obtain ⟨w5,hw5,run⟩ := bind_success _ _ _ run
           split at run
           · cases run
           · rename_i bound5
             obtain ⟨w6,hw6,run⟩ := bind_success _ _ _ run
             split at run
             · cases run
             · rename_i bound6
               obtain ⟨w7,hw7,run⟩ := bind_success _ _ _ run
               split at run
               · cases run
               · rename_i bound7
                 have same := Option.some.inj (Result.ok.inj run)
                 subst out
                 simp only [FIo_Native.aspis_core.field.P] at bound0 bound1 bound2 bound3 bound4 bound5 bound6 bound7
                 exact ⟨⟨⟨Nat.lt_of_not_ge bound0,Nat.lt_of_not_ge bound1⟩,⟨Nat.lt_of_not_ge bound2,Nat.lt_of_not_ge bound3⟩⟩,
                  ⟨⟨Nat.lt_of_not_ge bound4,Nat.lt_of_not_ge bound5⟩,⟨Nat.lt_of_not_ge bound6,Nat.lt_of_not_ge bound7⟩⟩⟩

theorem bytes (input : Slice U8) (out : Native)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes input=ok (some out)) :
 NFN_LPi_FieldValues.canonE out := by
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes at run
 dsimp only at run
 split at run
 · cases run
 · iterate 40 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
   exact limbs _ out run

theorem field (input : Slice U8) (i : Usize) (out : Native)
 (run : FIo_Native.weights.field input i=ok out) : NFN_LPi_FieldValues.canonE out := by
 unfold FIo_Native.weights.field at run
 iterate 4 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 obtain ⟨option,parsed,run⟩ := bind_success _ _ _ run
 cases option with
 | none => cases run
 | some raw =>
  have same : raw=out := Result.ok.inj run
  subst out
  exact bytes _ raw parsed

def read (input : Slice U8) (i : Usize) : Result AspisR1Stage2.Stage2Finish.E := do
 let out ← FIo_Native.weights.field input i
 ok (FIo_Install.fromE out)

theorem read_canonical (input : Slice U8) (i : Usize) (out : AspisR1Stage2.Stage2Finish.E)
 (run : read input i=ok out) : Port4C_QueryArithmetic.CanonE out := by
 obtain ⟨native,hn,he⟩ := bind_success _ _ _ run
 have same := Result.ok.inj he
 subst out
 have h := field input i native hn
 exact ⟨⟨h.1.1.1,h.1.1.2,h.1.2.1,h.1.2.2⟩,⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩⟩
#print axioms limbs
#print axioms bytes
#print axioms field
#print axioms read_canonical
end AspisR1.NFS_ReadCanonical
end
