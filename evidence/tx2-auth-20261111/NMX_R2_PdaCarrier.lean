import NMX_R2_PrimitiveInstall
import NMX_R2_ObserveResult
import NMX_R2_Observation
set_option autoImplicit false
noncomputable section
namespace NMX_R2_PdaCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier NMX_R2_ObserveResult

def mapped (raw : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :
 core.result.Result solana_pubkey.Pubkey solana_program_error.ProgramError :=
 match raw with | .Ok k => .Ok k | .Err _ => .Err .InvalidAccountData

def outcome (base : Ops) (env : RSL.Env) (seeds : Slice (Slice U8))
 (program : solana_pubkey.Pubkey) : RSL.Obs (Except RSL.ProgramError RSL.B32) :=
 let raw := do let r ← (NMX_R2_PrimitiveInstall.install base env).op38 seeds program; ok (mapped r)
 observe key raw [.pda (seeds.val.map bytes) (key program)
  (env.pda (seeds.val.map bytes) (key program))]

theorem reply (base : Ops) (env : RSL.Env) (seeds : Slice (Slice U8))
 (program : solana_pubkey.Pubkey) :
 outcome base env seeds program =
 ⟨.ret (match env.pda (seeds.val.map bytes) (key program) with
 | none => .error .invalidAccountData
 | some r => .ok r),
 [.pda (seeds.val.map bytes) (key program) (env.pda (seeds.val.map bytes) (key program))]⟩ := by
 unfold outcome
 rw [NMX_R2_PrimitiveInstall.pda]
 cases h : env.pda (seeds.val.map bytes) (key program) with
 | none => rfl
 | some r =>
   simp only [bind_tc_ok,mapped,observe,NMX_R2_Carrier.reply,NMX_R2_InverseBytes.key_roundtrip]

/-- Observable syscall event, including an error reply, at its source position. -/
theorem call (seeds : List RSL.Bytes) (program : RSL.B32) (env : RSL.Env) :
 RSL.pdaCall seeds program env
  ⟨.ret (env.pda seeds program),[.pda seeds program (env.pda seeds program)]⟩ := by
 unfold RSL.pdaCall
 exact Or.inl ⟨env.pda seeds program,[],
  ⟨.ret (env.pda seeds program),[.pda seeds program (env.pda seeds program)]⟩,
  rfl,Or.inl ⟨(),[.pda seeds program (env.pda seeds program)],
   ⟨.ret (env.pda seeds program),[]⟩,rfl,rfl,rfl⟩,rfl⟩
#print axioms reply
#print axioms call
end NMX_R2_PdaCarrier
end
