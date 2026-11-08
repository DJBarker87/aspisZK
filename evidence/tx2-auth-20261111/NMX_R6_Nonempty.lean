import NMX_R6_Children
import NMX_R6_Clone
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Nonempty
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

local instance : MonadLift Result Result where
 monadLift := id

variable {A B : Type}

def Live {A : Type} (m : RSL.Spec A) : Prop := ∀ env, ∃ o, m env o

theorem lift (r : Result A) : Live (liftResult r) :=
 fun env => ⟨NMX_R6_Observation.scalar r,NMX_R6_Observation.lift r env⟩

theorem pure (a : A) : Live (RSL.Spec.pure a) := fun _ => ⟨⟨.ret a,[]⟩,rfl⟩

theorem bind (m : RSL.Spec A) (next : A → RSL.Spec B)
 (hm : Live m) (hn : ∀ a, Live (next a)) : Live (RSL.Spec.bind m next) := by
 intro env
 obtain ⟨o,run⟩ := hm env
 let k := fun a => Classical.choose (hn a env)
 exact ⟨NMX_R6_Observation.bind o k,
  NMX_R6_Observation.member m next env o k run (fun a => Classical.choose_spec (hn a env))⟩

theorem mapped (f : A → B) (m : RSL.Spec A) (h : Live m) : Live (RSL.Spec.map f m) := by
 apply bind _ _ h
 intro a
 exact pure _

theorem auth (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 Live (NMX_R4_NMS233.typed choices program accounts pool lane slot) := by
 intro env
 exact ⟨_,rfl⟩

theorem scan (b : Slice U8) : Live (NMS_R2N_ScanSites.interpreted b) := by
 intro env
 exact ⟨NMX_R6_Observation.scalar (NMS_R2N_ScanSites.scan (M := Result) (ok ()) b),
  NMX_R6_ScanComplete.complete b env⟩

theorem reconstruct (q : LIBB_PoolCarriers.Request) (a : LIBB_AuthCarrier.Raw)
 (c : LIBB_PoolCarriers.Afterstate) : Live (NMS_R2N_ReconstructSites.meaning q a c) :=
 fun env => ⟨_,NMX_R6_Children.reconstruct_complete q a c env⟩

theorem clone (e : solana_program_error.ProgramError) : Live (NMS_R2N_GetterMeaning.clone e) := by
 unfold NMS_R2N_GetterMeaning.clone
 apply mapped
 generalize NMS_R2N_RSLError.error e = error
 cases error <;> try exact pure _
 rename_i text
 simp only [NMS_R2N_CloneReference.clone]
 split
 · exact pure _
 · apply bind _ _ (fun env => ⟨⟨.ret (),[]⟩,Or.inl rfl⟩)
   intro unit
   exact pure _

theorem getter (a : r1_pool_adapter.owned.OwnedAccount) : Live (NMS_R2N_GetterMeaning.meaning a) := by
 unfold NMS_R2N_GetterMeaning.meaning NMS_R2N_GetterMeaning.get
 cases a.bytes with
 | Ok b => exact pure _
 | Err e =>
   apply bind _ _ (clone e)
   intro copied
   exact pure _

#print axioms lift
#print axioms pure
#print axioms bind
#print axioms mapped
#print axioms auth
#print axioms scan
#print axioms reconstruct
#print axioms clone
#print axioms getter
end NMX_R6_Nonempty
end
