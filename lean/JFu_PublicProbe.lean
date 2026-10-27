import S6N_Installation
import JFx_NativeBytes
import JFv_TranscriptInitial
set_option autoImplicit false
open Aeneas Aeneas.Std Result
#eval match AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 AspisR1.JFx_NativeBytes.publicInput with
  | .ok (.Ok _) => "decoder accepts retained public1880"
  | .ok (.Err _) => "decoder rejects retained public1880"
  | .fail _ => "decoder fails retained public1880"
  | .div => "decoder diverges retained public1880"
#print AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1
#print AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_transfer_statement_boxed_v1
#print AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
