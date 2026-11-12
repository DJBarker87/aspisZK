-- stub for X2c's textual check (fv_x2c_emission_checks.py reads this file for the boundary's axiom)
axiom account_write.write_account_data_v1 : solana_account_info.AccountInfo → Std.Usize → Std.Usize → Slice Std.U8 → Result (core.result.Result Unit solana_program_error.ProgramError)
