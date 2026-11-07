import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_309
open RSL PCM
inductive Error where
  | wrongLength | wrongMagic | wrongVersion | nonZeroReserved
  | invalidAmount | invalidPayloadLength | nonCanonicalDigest
  deriving DecidableEq

def digest (b : Bytes) : Option Digest :=
  let ws := (List.range 8).map fun i =>
    le32 (b.getD (4*i) 0) (b.getD (4*i+1) 0) (b.getD (4*i+2) 0) (b.getD (4*i+3) 0)
  if ws.all (fun w => decide (w < P31)) then some ws else none

def model (bytes : Bytes) : Except Error DepositRequest := do
  if bytes.length < 80 || bytes.length > 592 then throw .wrongLength
  if bytes.take 4 != [65,83,56,68] then throw .wrongMagic
  if bytes.getD 4 0 != 1 then throw .wrongVersion
  if bytes.getD 5 0 != 0 || slice bytes 44 48 != [0,0,0,0] then throw .nonZeroReserved
  let declared := (bytes.getD 6 0).toNat + 256 * (bytes.getD 7 0).toNat
  if declared > 512 then throw .invalidPayloadLength
  if bytes.length != 80 + declared then throw .wrongLength
  let owner ← match digest (slice bytes 8 40) with
    | some v => pure v | none => throw .nonCanonicalDigest
  let salt ← match digest (slice bytes 48 80) with
    | some v => pure v | none => throw .nonCanonicalDigest
  let amount := le32 (bytes.getD 40 0) (bytes.getD 41 0) (bytes.getD 42 0) (bytes.getD 43 0)
  if amount == 0 || amount ≥ 1073741824 then throw .invalidAmount
  pure ⟨owner,amount,salt,bytes.drop 80⟩

def RowSpec (impl : Bytes → Env → Obs (Except Error DepositRequest)) : Prop :=
  ∀ b env, impl b env = ⟨.ret (model b),[]⟩

/-- This helper returns its actual format enum; only caller 328 maps it to
InvalidInstructionData. A constant different enum error is rejected. -/
theorem rejects_wrong_error :
    ¬ RowSpec (fun _ _ => ⟨.ret (.error .wrongMagic),[]⟩) := by
  intro h
  have he := h [] env0
  have hm : model [] = .error .wrongLength := rfl
  rw [hm] at he
  cases he

#print axioms rejects_wrong_error
end PCM_POOL_309
