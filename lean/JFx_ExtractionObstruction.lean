import CPH_FixtureData
import AdapterRwAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_ExtractionObstruction
open Aeneas Aeneas.Std Result

/-- The source cannot accept an empty account list, for ANY operation dictionary.
Use the proved accepted-call inversion, without reducing the caller body. -/
theorem empty_accounts_reject (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (saved : alloc.vec.Vec U8) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned ops program
      (⟨[],by simp⟩ : S2W_ExtractionBoundary.Accounts) data ≠ ok (.Ok saved) := by
  intro success
  obtain ⟨pa,pu,pub,raw,stmt,sem,selected,split,first,rest⟩ :=
    AdapterRw.Accepted.first_call ops program _ data saved success
  simp only [Slice.index_usize] at first
  cases first

/-- No constant-success native TX1 can satisfy the universally quantified D188
stage1 equality. This obstruction is independent of hash, bytes and allocator. -/
theorem constant_success_not_extracted (ops : AdapterRw.Ops)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (saved : alloc.vec.Vec U8) :
    ¬ S2W_DigestExtraction.AeneasExtraction ops
      (fun _ _ _ => ok (.Ok saved)) native2 hashv := by
  intro extraction
  have eq := extraction.stage1 CPH_FixtureData.id
    (⟨[],by simp⟩ : S2W_ExtractionBoundary.Accounts) (⟨[],by simp⟩ : Slice U8)
  exact empty_accounts_reject ops _ _ saved eq.symm

/-- The previously inhabited CPH runtime/game/wrapper model cannot be extended
with the top theorem's extraction premise, for any configuration whatsoever.
This does not assert that all possible CPH_Top witnesses are inconsistent. -/
theorem cph_fixture_not_extracted (ops : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ¬ S2W_DigestExtraction.AeneasExtraction ops CPH_FixtureData.n1
      CPH_FixtureData.n2 hashv :=
  constant_success_not_extracted ops CPH_FixtureData.n2 hashv CPH_FixtureData.saved

#print axioms empty_accounts_reject
#print axioms constant_success_not_extracted
#print axioms cph_fixture_not_extracted
end AspisR1.JFx_ExtractionObstruction
end
