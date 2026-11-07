import AdapterRwTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_SdkPda
open AdapterRw
abbrev Seeds := Slice (Slice U8)
/-- Exact SDK syscall arguments. Descriptor identity denotes the same ordered slice. -/
structure Request where
  seeds : Seeds
  program : solana_pubkey.Pubkey
/-- SDK syscall status and the bytes written to the caller-owned output region. -/
structure Reply where
  status : Nat
  address : solana_pubkey.Pubkey
  bump : U8

def createReply (r : Reply) : Result
    (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :=
  if r.status = 0 then ok (.Ok r.address)
  else if r.status = 1 then ok (.Err .InvalidSeeds)
  else if r.status = 2 then ok (.Err .IllegalOwner)
  else fail .panic

def tryFindReply (r : Reply) : Option (solana_pubkey.Pubkey × U8) :=
  if r.status = 0 then some (r.address, r.bump) else none

def findReply (r : Reply) : Result (solana_pubkey.Pubkey × U8) :=
  match tryFindReply r with
  | some pair => ok pair
  | none => fail .panic

def seedValid (seed : List U8) : Bool := decide (seed.length ≤ 32)
def validate : List (List U8) → Bool
  | [] => true
  | s :: ss => seedValid s && validate ss

/-- One arbitrary validation step; its native counterpart must use arbitrary pre-state. -/
theorem validation_step (s : List U8) (ss : List (List U8)) :
  validate (s :: ss) = (decide (s.length ≤ 32) && validate ss) := rfl

theorem validation_all (seeds : List (List U8)) :
  validate seeds = true ↔ ∀ s ∈ seeds, s.length ≤ 32 := by
  induction seeds with
  | nil => simp [validate]
  | cons s ss ih => simp [validate, seedValid, ih]

/-- The request is passed unchanged; the syscall is a quantified reply, never a PDA value law. -/
def create (request : Request) (reply : Reply) := (request, createReply reply)
def find (request : Request) (reply : Reply) := (request, findReply reply)

theorem create_forward (q : Request) (r : Reply) :
  create q r = (q, createReply r) := rfl

theorem find_forward (q : Request) (r : Reply) :
  find q r = (q, findReply r) := rfl

theorem create_ok (r : Reply) (h : r.status = 0) :
  createReply r = ok (.Ok r.address) := by simp [createReply,h]

theorem find_ok (r : Reply) (h : r.status = 0) :
  findReply r = ok (r.address,r.bump) := by simp [findReply,tryFindReply,h]

#print axioms validation_step
#print axioms validation_all
#print axioms create_forward
#print axioms find_forward
#print axioms create_ok
#print axioms find_ok
end PCG_SdkPda
