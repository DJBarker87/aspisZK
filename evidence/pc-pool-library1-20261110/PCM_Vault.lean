import PCM_Carriers
import PCM_SdkOps
set_option autoImplicit false
namespace PCM.Vault
open RSL Computation
structure Mint where
  supply : UInt64
  decimals : UInt8
structure Token where
  mint : B32
  authority : B32
  amount : UInt64
  has_delegate : Bool
  is_native : Bool
  delegated_amount : UInt64
  has_close_authority : Bool

def TOKEN_ID : B32 := mkB32
  [6,221,246,225,215,101,161,147,217,203,225,70,206,235,121,172,28,180,133,237,95,91,55,145,58,140,245,133,126,255,0,169] rfl

def five (accounts : List AccountInfo) : Computation (AccountInfo × AccountInfo × AccountInfo × AccountInfo × AccountInfo) :=
  match accounts with
  | [a,b,c,d,e] => Computation.pure (a,b,c,d,e)
  | _ => Computation.throw (if accounts.length < 5 then .notEnoughAccountKeys else .invalidArgument)

structure Children where
  ownedAccount : Child (AccountInfo × Bool) Unit
  mint : Child Bytes Mint
  token : Child Bytes Token
  vaultAddress : Child (B32 × B32) (B32 × UInt8)
  authorityAddress : Child (B32 × B32) (B32 × UInt8)
  storedBumpMatches : Child (List Bytes × B32 × B32) Bool

def readMint (C : Children) (a : AccountInfo) : Computation Mint :=
  guardScope a .shared fun _ => do
    let s ← get
    C.mint.call (s.bytes a)
def readToken (C : Children) (a : AccountInfo) : Computation Token :=
  guardScope a .shared fun _ => do
    let s ← get
    C.token.call (s.bytes a)

def tokenProgramBad (identity : PoolIdentity) (a : AccountInfo) : Bool :=
  identity.token_program != TOKEN_ID || a.key != TOKEN_ID ||
    !a.executable || a.is_signer || a.is_writable

def newInstruction (source mint destination authority : B32) (amount : UInt64)
    (decimals : UInt8) : Computation Instruction := do
  alloc
  let data := [12] ++ u64le amount ++ [decimals]
  alloc
  Computation.pure ⟨TOKEN_ID,[⟨source,false,true⟩,⟨mint,false,false⟩,
    ⟨destination,false,true⟩,⟨authority,true,false⟩],data⟩
end PCM.Vault
