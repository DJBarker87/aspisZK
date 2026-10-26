import PoolS2_MasterRead
set_option autoImplicit false
namespace AspisR1.PoolS2_MasterErrors
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterRead

theorem metadata_error (decode : Decode) (pda : Ops) (program : Key) (a : Account) (w : Bool)
    (e : ProgramError)
    (h : Hiq_PoolSource.history.require_program_account a program w = ok (.Err e)) :
    run decode pda program a w = ok (.Err e) := by simp [run,h]

theorem signer_error (decode : Decode) (pda : Ops) (program : Key) (a : Account) (w : Bool)
    (h : Hiq_PoolSource.history.require_program_account a program w = ok (.Ok ()))
    (signer : a.is_signer = true) :
    run decode pda program a w = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  simp [run,h,signer]

theorem read_error (decode : Decode) (pda : Ops) (program : Key) (a : Account) (w : Bool)
    (e : ProgramError)
    (h : Hiq_PoolSource.history.require_program_account a program w = ok (.Ok ()))
    (signer : a.is_signer = false) (read : a.bytes = .Err e) :
    run decode pda program a w = ok (.Err e) := by simp [run,h,signer,read]

theorem decoder_error (decode : Decode) (pda : Ops) (program : Key) (a : Account) (w : Bool)
    (bytes : alloc.vec.Vec U8) (e : FormatError)
    (h : Hiq_PoolSource.history.require_program_account a program w = ok (.Ok ()))
    (signer : a.is_signer = false) (read : a.bytes = .Ok bytes)
    (decoded : decode bytes.deref = ok (.Err e)) :
    run decode pda program a w = ok (.Err invalidType) := by simp [run,h,signer,read,decoded]

#print axioms metadata_error
#print axioms signer_error
#print axioms read_error
#print axioms decoder_error
end AspisR1.PoolS2_MasterErrors
