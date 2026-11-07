import NNF_Dispatch
set_option autoImplicit false
namespace NNF_Reify
open RSL Aeneas Aeneas.Std AspisR1 NNF_Carrier NNF_Dispatch
/-- Exact Pubkey representation: all 32 bytes, not a hash or chosen key. -/
def program (p : B32) : Hiq_DispatchSource.Key :=
  ⟨bytes p.bytes, by simpa [bytes] using p.len⟩
def data (d : Bytes) (h : d.length ≤ Usize.max) : Slice U8 :=
  ⟨bytes d, by simpa [bytes] using h⟩
/-- Reification preserves the full account list, every descriptor field and
all instruction bytes. Bounds are Rust slice representability facts, used
ONLY by the carrier lemma, never by a dispatcher RowSpec. -/
theorem args_inverse (a : TX2_240.Args)
    (ha : a.accounts.length ≤ Usize.max) (hd : a.data.length ≤ Usize.max) :
    args (program a.program_id) ⟨a.accounts, ha⟩ (data a.data hd) = a := by
  rcases a with ⟨⟨p, hp⟩, accts, d⟩
  simp [args, program, data, bytes_inverse]

/-- Fresh NMW process body interpreted over the COMPLETE RSL observation.
Every child use is at the SAME original p/accounts/data/prestate/env. -/
theorem process_source (f1 f2 : Child) (a : TX2_240.Args) (s : SdkState) (env : Env)
    (ha : a.accounts.length ≤ Usize.max) (hd : a.data.length ≤ Usize.max)
    (admitted : TX2_221.admitted a.data = true) :
    NMW_Symbolic.process (ops f1 f2 s env) (program a.program_id)
      ⟨a.accounts, ha⟩ (data a.data hd) = .ok (process f1 f2 a s env) := by
  have h : TX2_221.admitted (unbytes (data a.data hd).val) = true := by
    simpa only [data, bytes_inverse] using admitted
  have t := process_emitted f1 f2 s env (program a.program_id)
    ⟨a.accounts, ha⟩ (data a.data hd) h
  rwa [args_inverse] at t

theorem entry_source (f1 f2 : Child) (a : TX2_240.Args) (s : SdkState) (env : Env)
    (ha : a.accounts.length ≤ Usize.max) (hd : a.data.length ≤ Usize.max) :
    NMW_Symbolic.entry (ops f1 f2 s env)
      ⟨.ret (.error .invalidInstructionData, s), []⟩ (program a.program_id)
      ⟨a.accounts, ha⟩ (data a.data hd) = .ok (entry (process f1 f2) a s env) := by
  have t := entry_emitted f1 f2 s env (program a.program_id)
    ⟨a.accounts, ha⟩ (data a.data hd)
  rwa [args_inverse] at t
#print axioms args_inverse
#print axioms process_source
#print axioms entry_source
end NNF_Reify
