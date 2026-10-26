import PoolU_Step
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolU_CopyTail
open Aeneas Aeneas.Std Result PoolU_Step PoolW_Store

/-- Only the copy continuation of F2183–2188. Borrow acquisition and release
are separate source leaves. The starting store is the one AFTER any System CPI,
not the pre-invocation store. No claim about lamports across CPI is made. -/
def copies {M : Type} (master checkpoint : Key) (masterImage checkpointImage : Bytes) :
    Step (Store M) AdapterRw.solana_program_error.ProgramError Unit :=
  fun store => (ok (.Ok ()),copyBoth store master checkpoint masterImage checkpointImage)

/-- Compose an arbitrary reached prefix without post-selecting a different
successful prefix. The prefix result itself supplies both copy images. -/
def afterPrefix {M : Type} (master checkpoint : Key)
    (prelude : Step (Store M) AdapterRw.solana_program_error.ProgramError (Bytes × Bytes)) :
    Step (Store M) AdapterRw.solana_program_error.ProgramError Unit :=
  bind prelude (fun images => copies master checkpoint images.1 images.2)

theorem accepted {M : Type} (master checkpoint : Key)
    (prelude : Step (Store M) AdapterRw.solana_program_error.ProgramError (Bytes × Bytes))
    (before after : Store M) (unique : checkpoint ≠ master)
    (h : afterPrefix master checkpoint prelude before = (ok (.Ok ()),after)) :
    ∃ images postPrefix,
      prelude before = (ok (.Ok images),postPrefix) ∧
      after = copyBoth postPrefix master checkpoint images.1 images.2 ∧
      (after checkpoint).data = images.2 ∧ (after master).data = images.1 ∧
      (∀ address, address ≠ master → address ≠ checkpoint → after address = postPrefix address) ∧
      (∀ address, (after address).metadata = (postPrefix address).metadata) := by
  rcases (accepted_bind prelude _ before after ()).mp h with ⟨images,postPrefix,hp,hc⟩
  have storeEq : after = copyBoth postPrefix master checkpoint images.1 images.2 := by
    exact (Prod.mk.inj hc).2.symm
  refine ⟨images,postPrefix,hp,storeEq,?_,?_,?_,?_⟩
  · rw [storeEq]; exact checkpoint_copy _ _ _ _ _ unique
  · rw [storeEq]; exact master_copy _ _ _ _ _
  · intro address hm hc; rw [storeEq]; exact frame _ _ _ _ _ _ hm hc
  · intro address; rw [storeEq]; exact all_metadata _ _ _ _ _ _

theorem rejected_prefix {M : Type} (master checkpoint : Key)
    (prelude : Step (Store M) AdapterRw.solana_program_error.ProgramError (Bytes × Bytes))
    (before stopped : Store M) (e : AdapterRw.solana_program_error.ProgramError)
    (h : prelude before = (ok (.Err e),stopped)) :
    afterPrefix master checkpoint prelude before = (ok (.Err e),stopped) :=
  error_prefix _ _ _ _ _ h

#print axioms accepted
#print axioms rejected_prefix
end AspisR1.PoolU_CopyTail
end
