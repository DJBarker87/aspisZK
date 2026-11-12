-- X2d item 2: planted POSITIVE cases for fv_emit_read_after_write.py, in the form Aeneas emits (do blocks, match
-- arms beginning with '|', 'if' / 'then' / 'else' on their own lines, loops through the 'loop' combinator, trait
-- methods through an instance parameter). Each root below performs a read of account data after a write on some
-- path; the tool must report every one of them. Not compiled (the shapes matter, not the types).
namespace Planted

/-- a helper that only reads -/
def test.reads_data (ai : solana_account_info.AccountInfo) : Result Std.Usize := do
  let n ← solana_account_info.AccountInfo.data_len ai
  ok n

/-- P1: write, then a direct read in the Ok arm. -/
def test.p1_write_then_read
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← account_write.write_account_data_v1 ai 0#usize 8#usize s
  match r with
  | core.result.Result.Ok _ =>
    let (r1, _) ← solana_account_info.AccountInfo.try_borrow_data ai
    ok (core.result.Result.Ok ())
  | core.result.Result.Err _ => ok r

/-- P2: write, then a call of a definition that reads. -/
def test.p2_write_then_call_reader
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← account_write.write_account_data_v1 ai 0#usize 8#usize s
  let n ← test.reads_data ai
  ok r

/-- P3: a write on one branch only, then a read after the branches join. -/
def test.p3_write_on_one_branch_then_read
  (b : Bool) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ←
    if b
    then
      account_write.write_account_data_v1 ai 0#usize 8#usize s
    else ok (core.result.Result.Ok ())
  let e ← solana_account_info.AccountInfo.data_is_empty ai
  ok r

/-- P4 (loop body): reads, then writes; the loop runs it again, so a later iteration reads after a write. -/
def test.p4_loop.body
  (i : Std.Usize) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (ControlFlow Std.Usize Unit)
  := do
  let n ← solana_account_info.AccountInfo.data_len ai
  if i < n
  then
    let r ← account_write.write_account_data_v1 ai i (i + 1#usize) s
    ok (cont (i + 1#usize))
  else ok (done ())

def test.p4_loop
  (i : Std.Usize) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result Unit
  := do
  loop
    (fun i1 =>
      test.p4_loop.body i1 ai s)
    i

/-- P5: a trait method called through the instance parameter after a write; the only emitted instance's method reads. -/
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

def test.p5_write_then_trait_method
  {H : Type _} (testHostInst : test.Host H) (host : H)
  (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← account_write.write_account_data_v1 ai 0#usize 8#usize s
  let (n, host1) ← testHostInst.look host ai
  ok r

/-- P6: the write in one match arm, the read after the match. -/
def test.p6_match_arm_write_then_read
  (o : Option Std.U8) (ai : solana_account_info.AccountInfo) (s : Slice Std.U8) :
  Result Unit
  := do
  let r ←
    match o with
    | none => ok (core.result.Result.Ok ())
    | some _ => account_write.write_account_data_v1 ai 0#usize 8#usize s
  let l ← solana_account_info.AccountInfo.impl.lamports ai
  ok ()

end Planted
