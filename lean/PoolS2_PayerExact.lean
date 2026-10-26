import PoolS2_Payer
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PayerExact
open Aeneas Aeneas.Std Result PoolS2_PrefixSource PoolS2_Payer

theorem ready (payer system : Account) (hp : PayerOK payer) (hs : SystemOK system) :
    processor.require_payer_and_system_program payer system = ok (.Ok ()) := by
  classical
  rcases hp with ⟨signer,writable,executable,owner⟩
  rcases hs with ⟨key,loader,systemExecutable,systemSigner,systemWritable⟩
  simp [processor.require_payer_and_system_program,Hiq_PoolSource.keyNe,Hist_Authority.keyEq,
    signer,writable,executable,owner,key,loader,systemExecutable,systemSigner,systemWritable]

theorem accepted_iff (payer system : Account) :
    processor.require_payer_and_system_program payer system = ok (.Ok ()) ↔
      PayerOK payer ∧ SystemOK system :=
  ⟨PoolS2_Payer.accepted payer system,fun h => ready payer system h.1 h.2⟩

#print axioms ready
#print axioms accepted_iff
end AspisR1.PoolS2_PayerExact
end
