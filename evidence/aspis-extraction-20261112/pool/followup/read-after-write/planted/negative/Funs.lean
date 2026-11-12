-- X2d item 2: planted NEGATIVE cases for fv_emit_read_after_write.py, in the form Aeneas emits. No root below reads
-- account data after a write on any path; the tool must pass every one. N1 is the shape X2c's textual check
-- flagged in processor.dispatch_pool_instruction_v1 (handlers on mutually exclusive branches, a later branch's
-- handler reading before its own writes); N2 is the shape it flagged in pair_forest.process_pair_forest_terminal_v1
-- (an instance whose method reads, passed as an argument of the same call as a handler that writes after calling
-- that method). Not compiled.
namespace Planted

/-- a handler that writes only -/
def test.handler_writes
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  account_write.write_account_data_v1 ai 0#usize 8#usize s

/-- a handler that reads, then writes -/
def test.handler_reads_then_writes
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let n ← solana_account_info.AccountInfo.data_len ai
  if n < 8#usize
  then ok (core.result.Result.Err solana_program_error.ProgramError.AccountDataTooSmall)
  else
    account_write.write_account_data_v1 ai 0#usize 8#usize s

/-- N1: dispatch over exclusive branches; the writing handler textually precedes the reading one. -/
def test.n1_dispatch
  (magic : Slice Std.U8) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 magic
      (Array.make 4#usize [ 65#u8, 83#u8, 56#u8, 73#u8 ])
  if b
  then
    let r ← test.handler_writes ai s
    ok r
  else
    let b1 ←
      Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 magic
        (Array.make 4#usize [ 65#u8, 83#u8, 56#u8, 67#u8 ])
    if b1
    then
      let r ← test.handler_reads_then_writes ai s
      ok r
    else
      match magic with
      | _ =>
        let r ← test.handler_writes ai s
        ok r

/-- N2: an instance whose method reads, passed to a generic handler that calls the method, then writes. -/
structure test.Host (Self : Type _) where
  look : Self → solana_account_info.AccountInfo → Result (Std.Usize × Self)

def test.ReadingHost.Insts.TestHost.look
  (self : test.ReadingHost) (ai : solana_account_info.AccountInfo) : Result (Std.Usize × test.ReadingHost) := do
  let n ← solana_account_info.AccountInfo.data_len ai
  ok (n, self)

@[reducible]
def test.ReadingHost.Insts.TestHost : test.Host test.ReadingHost := {
  look := test.ReadingHost.Insts.TestHost.look
}

def test.generic_handler
  {H : Type _} (testHostInst : test.Host H) (host : H)
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let (n, host1) ← testHostInst.look host ai
  let r ← account_write.write_account_data_v1 ai 0#usize 8#usize s
  ok r

def test.n2_instance_argument
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  test.generic_handler test.ReadingHost.Insts.TestHost () ai s

/-- N3: match arms that each read before their own write; nothing after the match. -/
def test.n3_match_arms
  (o : Option Std.U8) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  match o with
  | none =>
    let r ← test.handler_reads_then_writes ai s
    ok r
  | some _ =>
    let e ← solana_account_info.AccountInfo.data_is_empty ai
    let r ← test.handler_writes ai s
    match r with
    | core.result.Result.Ok _ => ok r
    | core.result.Result.Err _ => ok r

end Planted
