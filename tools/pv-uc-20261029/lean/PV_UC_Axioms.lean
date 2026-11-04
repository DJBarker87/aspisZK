import PV_UC_RawAudit
import PV_UC_FormattingObstruction
import PVUCDecoder.Types

open Lean Elab Command

-- This audits the compiled diagnostic and type roots only. Full-entry and
-- decoder Funs are unavailable after their recorded compilation refusals.
#print axioms PV_UC_FormattingObstruction.fdArguments_equal
#print axioms PV_UC_FormattingObstruction.no_faithful_fd_formatter
#print axioms PV_UC_Decoder.wallet.Wallet

run_cmd do
  let dir := "/home/dombarker/project-offloads/codex-pv-uc-20261029/final-gates/axioms"
  liftIO <| IO.FS.createDirAll dir
  PV_UC_RawAudit.audit ``PV_UC_FormattingObstruction.fdArguments_equal
    (dir ++ "/fdArguments_equal")
  PV_UC_RawAudit.audit ``PV_UC_FormattingObstruction.no_faithful_fd_formatter
    (dir ++ "/no_faithful_fd_formatter")
  PV_UC_RawAudit.audit ``PV_UC_Decoder.wallet.Wallet
    (dir ++ "/Wallet")
