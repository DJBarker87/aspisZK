import S6CurrentStage1FirstJoinV1
import S2Y_ForestPublic
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentNamedForestPort
open AspisR1.S2Y_ForestPublic AspisS6CurrentFirstInstallation

/-- Concrete full codec law at the exact named lead interface, including the
current first child. Other operations and native SDK effects remain separate. -/
theorem fullForestAcceptedRoundtrip (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) :
    FullForestAcceptedRoundtrip (install ops vops) := by
  intro original statement encoded decoded encoded_actual
  exact AspisS6CurrentCodecInstallation.installed_roundtrip
    {ops with op10:=current vops} original statement encoded decoded encoded_actual

/-- The original lead consumer now requires no separate full codec law.
Identity of the reconstructed statement and child-input retention are retained
exactly; no SDK or cross-transaction identity is inferred from codec equality. -/
theorem reconstructed_bytes (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (original : Slice U8) (decoded reconstructed : Statement)
    (encoded : Array U8 1880#usize)
    (decode : (install ops vops).op47 original=ok (.Ok decoded))
    (encode : (install ops vops).op22 reconstructed=ok (.Ok encoded))
    (identity : reconstructed=decoded) :
    AspisR1.MultiproofConeCanonical.bytesOf (Array.to_slice encoded).val =
      AspisR1.MultiproofConeCanonical.bytesOf original.val ∧
    (AspisR1.MultiproofConeCanonical.bytesOf original.val).length=1880 := by
  exact AspisR1.S2Y_ForestPublic.reconstructed_bytes (install ops vops)
    (fullForestAcceptedRoundtrip ops vops) original decoded reconstructed encoded decode encode identity

/-- Same accepted two-transaction owned consumer, with its full codec-law
premise discharged. Child retention and cross-transaction statement identity
remain explicit, exactly as in the lead consumer. -/
theorem owned_public_field (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (c : AspisR1.S2LeadInterface.Inputs Observer)
    (childInputRetention : AdapterRw.LeadInputs.ChildInputRetention (install ops vops) c)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts1 accounts2 : Slice AdapterRw.Cuts.Account) (data1 data2 : Slice U8)
    (checkpoint1 : alloc.vec.Vec U8) (slot : core.result.Result U64 AdapterRw.Cuts.PE)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops) program accounts1 data1 =
      ok (.Ok checkpoint1))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned (install ops vops) program accounts2 data2 slot =
      ok (.Ok ())) :
    ∃ publicAccount pub statement semantic proof1 split validated encoded proof2 checkpoint2,
      Slice.index_usize accounts1 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops vops) publicAccount = ok (.Ok pub) ∧
      (install ops vops).op47 pub = ok (.Ok statement) ∧
      AdapterRw.first_decoded (install ops vops) semantic pub proof1 split = ok (.Ok checkpoint1) ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (install ops vops) program accounts2 data2 slot =
        ok (.Ok validated) ∧
      (install ops vops).op22 validated.statement = ok (.Ok encoded) ∧
      (install ops vops).op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops))
        (Array.to_slice encoded) proof2 checkpoint2 () none = ok (.Ok ()) ∧
      (validated.statement = statement →
        AspisR1.MultiproofConeCanonical.bytesOf (Array.to_slice encoded).val =
          AspisR1.MultiproofConeCanonical.bytesOf pub.val ∧
        (AspisR1.MultiproofConeCanonical.bytesOf pub.val).length = 1880 ∧
        (∀ site, c.reached site → AspisR1.MultiproofConeCanonical.bytesOf (c.publicInput site).val =
          AspisR1.MultiproofConeCanonical.bytesOf pub.val)) := by
  exact AspisR1.S2Y_ForestPublic.owned_public_field (install ops vops) c
    (fullForestAcceptedRoundtrip ops vops) childInputRetention program accounts1 accounts2 data1 data2
    checkpoint1 slot accepted1 accepted2

#print axioms fullForestAcceptedRoundtrip
#print axioms reconstructed_bytes
#print axioms owned_public_field
end AspisS6CurrentNamedForestPort
