import NJE_RoundTrace
import NJA_Compress
import NJE_CountPacket

set_option autoImplicit false
noncomputable section
namespace NJE_CompressSeed
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K
abbrev State := NJE_RoundTrace.State

def seed (left right : Fin 8 → U32) (i : Fin 16) : U32 :=
 if h : i.val<8 then left ⟨i.val,h⟩ else
 if i.val=15 then NJE_AddValue.add (right 7) 1095962629#u32 else right ⟨i.val-8,by omega⟩

theorem value (left right : Fin 8 → U32)
 (hl : ∀ i, (left i).val<2147483647) (hr : ∀ i, (right i).val<2147483647) :
 NJE_RoundTrace.Canonical (seed left right) ∧
 NJE_RoundTrace.cast (seed left right)=
   NJA_Compress.seed (fun i => ((left i).val:K)) (fun i => ((right i).val:K)) := by
 have tweak := NJE_AddValue.law (right 7) 1095962629#u32 (hr 7) (by decide)
 have tweak_value := tweak.2.2
 change ((NJE_AddValue.add (right 7) 1095962629#u32).val:K)=((right 7).val:K)+(1095962629:Nat) at tweak_value
 norm_num only [Nat.cast_ofNat] at tweak_value
 constructor
 · intro i
   by_cases low : i.val<8
   · simpa only [seed,dif_pos low] using hl ⟨i.val,low⟩
   · by_cases last : i.val=15
     · simpa only [seed,dif_neg low,if_pos last] using tweak.2.1
     · simpa only [seed,dif_neg low,if_neg last] using hr ⟨i.val-8,by omega⟩
 · funext i
   by_cases low : i.val<8
   · simp only [NJE_RoundTrace.cast,seed,NJA_Compress.seed,dif_pos low]
   · by_cases last : i.val=15
     · simpa only [NJE_RoundTrace.cast,seed,NJA_Compress.seed,dif_neg low,if_pos last] using tweak_value
     · simp only [NJE_RoundTrace.cast,seed,NJA_Compress.seed,dif_neg low,if_neg last]

-- Complete Lean-side seed, permutation and8-limb result composition. Native
-- frozen-controller and no-op callback association remains an OPEN admission gate.
theorem result (left right : Fin 8 → U32)
 (hl : ∀ i, (left i).val<2147483647) (hr : ∀ i, (right i).val<2147483647)
 (states : Fin 23 → State)
 (bs : Nat → State) (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat)
 (leading : Nat → State) (start : states 0=leading 16)
 (initial_cut : NJE_ExternalStages.Cut (seed left right) bs sums args leading)
 (rounds : ∀ r, NJE_RoundTrace.Witness (states r.castSucc) (states r.succ) r) :
 ∀ i : Fin 8,
 ((states (Fin.last 22) ⟨i.val,by omega⟩).val:K)=
   R0P.nodeCompress (fun j => ((left j).val:K)) (fun j => ((right j).val:K)) i := by
 have joined := NJE_RoundTrace.composition (seed left right) states bs sums args leading start initial_cut rounds
 have seed_value := (value left right hl hr).2
 intro i
 have selected := congrFun joined.2 ⟨i.val,by omega⟩
 rw [seed_value,NJA_Compress.seed_model] at selected
 exact selected

#print value
#print axioms value
#print result
#print axioms result
end NJE_CompressSeed
end

#print NJE_CountPacket.assoc
#print axioms NJE_CountPacket.assoc
