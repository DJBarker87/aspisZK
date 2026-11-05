import NIL_Carriers
set_option autoImplicit false
noncomputable section
namespace NIY_NativeCuts
open Aeneas Aeneas.Std NIL_Carriers

/-! Reviewed cut transcriptions for NIY_tail_native.rs.txt. The pinned SHA256 is
in NIY_NATIVE_ASSOCIATION.json. These propositions are not native certificates.
They transcribe only the asserted selected values, tags, cursor and descriptor.
No pointer-to-byte-identity or complete parent execution fact is inferred here. -/

def byteAt (bytes : Slice U8) (cursor : Nat) : Nat :=
 ((bytes.val[cursor]?).map (fun b=>b.val)).getD 0

def wordAt (bytes : Slice U8) (cursor : Nat) : Nat :=
 byteAt bytes cursor + 256 * byteAt bytes (cursor+1) +
 65536 * byteAt bytes (cursor+2) + 16777216 * byteAt bytes (cursor+3)

def good4 (bytes : Slice U8) (cursor : Nat) : Prop :=
 wordAt bytes cursor < 2147483647 ∧ wordAt bytes (cursor+4) < 2147483647 ∧
 wordAt bytes (cursor+8) < 2147483647 ∧ wordAt bytes (cursor+12) < 2147483647

def good8 (bytes : Slice U8) (cursor : Nat) : Prop :=
 good4 bytes cursor ∧ good4 bytes (cursor+16)

def limbK (q : Fresh.K) (j : Nat) : Nat :=
 match j with
 | 0 => q.c0.a.val
 | 1 => q.c0.b.val
 | 2 => q.c1.a.val
 | _ => q.c1.b.val

def limbE (q : Fresh.E) (j : Nat) : Nat :=
 limbK (if j<4 then q.c0 else q.c1) (j%4)

/-- first_check C=0/1/2: "assert_eq!(state[j],bytes[80+j]^(if inv{1}else{0}));" and roots[0/1]
with offsets112/144. Each literal C is listed separately in the native matrix. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def firstByte (bytes : Slice U8) (offset : Nat) (j : Fin 32)
 (observed : U8) : Prop := observed.val=byteAt bytes (offset+j.val)

/-- first_check C=3: "assert_eq!(r.at,208^(if inv{1}else{0}));". 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def firstCursor (cursor : Usize) : Prop := cursor.val=208

/-- e_check C=0 and first_check C=4: "assert_eq!(reply.is_ok(),good^inv);";
"if let Err(error)=reply{assert_eq!(error,Error::Checkpoint);}".
Only e_check C=0 also asserts cursor=O+32. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def eReply (bytes : Slice U8) (offset : Nat)
 (reply : core.result.Result Fresh.E Fresh.Err) : Prop :=
 match reply with
 | .Ok _ => good8 bytes offset
 | .Err err => ¬good8 bytes offset ∧ err=.Checkpoint

/-- k_check C=0, same two assertions, with four words and cursor+16. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def kReply (bytes : Slice U8) (offset : Nat)
 (reply : core.result.Result Fresh.K Fresh.Err) : Prop :=
 match reply with
 | .Ok _ => good4 bytes offset
 | .Err err => ¬good4 bytes offset ∧ err=.Checkpoint

/-- e_check C=1 / first_check C=5: selected successful limb equals word(bytes,O+4*j). 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def eValue (bytes : Slice U8) (offset : Nat) (j : Fin 8)
 (reply : core.result.Result Fresh.E Fresh.Err) : Prop :=
 match reply with
 | .Ok x => limbE x j.val=wordAt bytes (offset+4*j.val)
 | .Err _ => True

/-- k_check C=1: selected successful limb equals word(bytes,cursor+4*j). 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def kValue (bytes : Slice U8) (offset : Nat) (j : Fin 4)
 (reply : core.result.Result Fresh.K Fresh.Err) : Prop :=
 match reply with
 | .Ok x => limbK x j.val=wordAt bytes (offset+4*j.val)
 | .Err _ => True

/-- The two descriptor assertions only: same address and length1768.
This explicitly does NOT assert byte equality from pointer equality. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def descriptor (beforeAddress afterAddress length : Nat) : Prop :=
 afterAddress=beforeAddress ∧ length=1768

/-- e_check C=0's additional unconditional cursor assertion. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def eCursor (offset : Nat) (cursor : Usize) : Prop := cursor.val=offset+32

/-- k_check C=0's additional unconditional cursor assertion. 
Harness NIY_tail_native.rs.txt SHA256 077982d6e290231fb3bc9b459b61d0fb0e947edc52ea36f96e99de594b522a01. Positive configuration: inv=false.
-/
def kCursor (offset : Nat) (cursor : Usize) : Prop := cursor.val=offset+16

#print axioms firstByte
#print axioms firstCursor
#print axioms eReply
#print axioms kReply
#print axioms eValue
#print axioms kValue
#print axioms descriptor
#print axioms eCursor
#print axioms kCursor
end NIY_NativeCuts
