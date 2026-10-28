import NDO_JHd_ReferenceSlots
import NDO_JHb_S2K_ByteEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_KeyComparison
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem equal (base : Ops) (key : solana_pubkey.Pubkey) :
    (JHd_ReferenceSlots.install base).op36 key key=ok true :=
  S2K.Equality.array_self _ S2K.Equality.u8_ne_self key
#print axioms equal

theorem different (base : Ops) (key : solana_pubkey.Pubkey) :
    core.cmp.PartialEq.ne.trait_default
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHd_ReferenceSlots.install base))
      key key=ok false := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
  change ((JHd_ReferenceSlots.install base).op36 key key >>= fun b=>ok (decide (¬b=true)))=ok false
  rw [equal,bind_tc_ok]
  rfl
#print axioms different
end AspisR1.JHj_KeyComparison
end
