import PV_UC_RawAudit
import PVUCDecoder.Funs
import PVUCBoundEntry.Funs
import PV_UC_PublicFormatting

open Lean Elab Command
#print axioms PV_UC_BoundEntry.main
#print axioms PV_UC_Decoder.wallet.decode_wallet_record
#print axioms PV_UC_PublicFormatting.walletPath_same_public
#print axioms PV_UC_PublicFormatting.stdout_recomputable
#print axioms PV_UC_PublicFormatting.pubkey_recomputable
#print axioms PV_UC_PublicFormatting.extracted_fd_formatter_public

run_cmd do
  let dir := "/home/dombarker/project-offloads/codex-pv-uc-20261029/final-gates/d561/axioms"
  liftIO <| IO.FS.createDirAll dir
  PV_UC_RawAudit.audit ``PV_UC_BoundEntry.main (dir ++ "/main")
  PV_UC_RawAudit.audit ``PV_UC_Decoder.wallet.decode_wallet_record (dir ++ "/decode_wallet_record")
  PV_UC_RawAudit.audit ``PV_UC_PublicFormatting.walletPath_same_public (dir ++ "/walletPath_same_public")
  PV_UC_RawAudit.audit ``PV_UC_PublicFormatting.stdout_recomputable (dir ++ "/stdout_recomputable")
  PV_UC_RawAudit.audit ``PV_UC_PublicFormatting.pubkey_recomputable (dir ++ "/pubkey_recomputable")
  PV_UC_RawAudit.audit ``PV_UC_PublicFormatting.extracted_fd_formatter_public (dir ++ "/extracted_fd_formatter_public")
