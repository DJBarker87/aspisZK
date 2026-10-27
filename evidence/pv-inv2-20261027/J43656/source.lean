import R1Z.PV_Inv_RawBankRead
set_option autoImplicit false
namespace R1Z.PV_Inv_RawBankList
open Aeneas Aeneas.Std Result
open ProverCommitM31Ops48 ProverCommitScalar48 (embed)
open PV_Inv_BankSource PV_Inv_RawBankRead

def reads (b : Banks U32) : List (Limb U32) → Result (List U32)
  | [] => ok []
  | l::ls => do
    let z ← PV_Inv_RawBankRead.read b l
    let zs ← reads b ls
    ok (z::zs)

theorem exact_reads (b : Banks U32) (hb : CanonicalBanks b) (ls : List (Limb U32))
    (hl : ∀ l ∈ ls, CanonicalLimb l) :
    ∃ zs, reads b ls = ok zs ∧ (∀ z ∈ zs, canonical z) ∧
      zs.map embed = ls.map (fun l => PV_Inv_BankSource.read (banks b) (limb l)) := by
  induction ls with
  | nil => exact ⟨[],rfl,by simp,rfl⟩
  | cons l ls ih =>
    obtain ⟨z,hz,hcz,hvz⟩ := exact_read b hb l (hl l (by simp))
    obtain ⟨zs,hrs,hcs,hvs⟩ := ih (fun l he => hl l (by simp [he]))
    refine ⟨z::zs,?_,?_,?_⟩
    · simp only [reads,hz,hrs,bind_tc_ok]
    · intro y hy
      rcases List.mem_cons.mp hy with he|he
      · subst y; exact hcz
      · exact hcs y he
    · simp only [List.map_cons,hvz,hvs]

#print axioms exact_reads
end R1Z.PV_Inv_RawBankList
