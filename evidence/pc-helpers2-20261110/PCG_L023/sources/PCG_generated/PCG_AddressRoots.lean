import PCG_RequestCarrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_AddressRoots
open AdapterRw PCG_AddressRef
abbrev Key := Array U8 32#usize
/-- The already quantified program-address runtime slot, not a PDA value law. -/
abbrev Op38 := PCG_SdkPda.Request → PCG_SdkPda.Reply
structure FindObservation where
  calls : List PCG_SdkPda.Request
  result : Result (Key × U8)

def nativeFind (build : Result Request) (op38 : Op38) : Result FindObservation := do
 let q ← build
 let observed := PCG_SdkPda.find (PCG_RequestCarrier.request q)
   (op38 (PCG_RequestCarrier.request q))
 ok ⟨[observed.1],observed.2⟩

structure StoredObservation where
 calls : List PCG_SdkPda.Request
 result : Result Bool

def toReference (reply : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :
 core.result.Result Key PdaError :=
 match reply with
 | .Ok address => .Ok address
 | .Err e => .Err (match e with
   | .MaxSeedLengthExceeded => .MaxSeedLengthExceeded
   | .InvalidSeeds => .InvalidSeeds
   | .IllegalOwner => .IllegalOwner)

theorem stored_reference (reply : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError)
 (key : Key) :
 stored_matches (toReference reply) key = ok (match reply with
  | .Ok address => decide (address.val = key.val)
  | .Err _ => false) := by
 rw [PCG_AddressLaws.stored_result]
 cases reply <;> rfl

noncomputable def nativeStored (q : PCG_SdkPda.Request) (key : Key) (op38 : Op38) : StoredObservation :=
 let execution := PCG_SdkPda.createRun q (op38 q)
 ⟨execution.calls, do
   let reply ← execution.result
   stored_matches (toReference reply) key⟩

/-- Complete Bool/abort and singleton raw-syscall trace at SAME seeds/program/key.
Its sole domain clause concerns the helper's own seed slices. -/
theorem row_379 (q : PCG_SdkPda.Request) (key : Key) (op38 : Op38)
 (domain : PCG_SdkPda.Domain q) :
 nativeStored q key op38 = ⟨[q],do
   let reply ← PCG_SdkPda.createReply (op38 q)
   ok (match reply with
    | .Ok address => decide (address.val = key.val)
    | .Err _ => false)⟩ := by
 unfold nativeStored
 rw [PCG_SdkPda.create_packet q (op38 q) domain]
 simp only [stored_reference]

#print axioms stored_reference
#print axioms row_379

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_374 (program pool : Key) (profile release : Key) (op38 : Op38) :
 nativeFind (request_374 program pool profile release) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_374 program pool profile release))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_374 program pool profile release)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_374 program pool profile release)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_374 program pool profile release)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_374 program pool profile release)).seeds.val.length = 4 := by
 constructor
 · rw [PCG_AddressLaws.request_374]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_374 program pool profile release).1]
   rfl
#print axioms row_374

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_375 (program pool : Key) (profile release : Key) (op38 : Op38) :
 nativeFind (request_375 program pool profile release) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_375 program pool profile release))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_375 program pool profile release)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_375 program pool profile release)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_375 program pool profile release)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_375 program pool profile release)).seeds.val.length = 4 := by
 constructor
 · rw [PCG_AddressLaws.request_375]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_375 program pool profile release).1]
   rfl
#print axioms row_375

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_376 (program pool : Key) (op38 : Op38) :
 nativeFind (request_376 program pool) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_376 program pool))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_376 program pool)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_376 program pool)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_376 program pool)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_376 program pool)).seeds.val.length = 2 := by
 constructor
 · rw [PCG_AddressLaws.request_376]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_376 program pool).1]
   rfl
#print axioms row_376

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_377 (program pool : Key) (op38 : Op38) :
 nativeFind (request_377 program pool) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_377 program pool))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_377 program pool)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_377 program pool)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_377 program pool)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_377 program pool)).seeds.val.length = 2 := by
 constructor
 · rw [PCG_AddressLaws.request_377]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_377 program pool).1]
   rfl
#print axioms row_377

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_390 (program pool : Key) (op38 : Op38) :
 nativeFind (request_390 program pool) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_390 program pool))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_390 program pool)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_390 program pool)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_390 program pool)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_390 program pool)).seeds.val.length = 2 := by
 constructor
 · rw [PCG_AddressLaws.request_390]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_390 program pool).1]
   rfl
#print axioms row_390

/-- Actual helper/native request reference, complete SDK reply/abort and ordered call. -/
theorem row_391 (program pool : Key) (op38 : Op38) :
 nativeFind (request_391 program pool) op38 =
   ok ⟨[(PCG_RequestCarrier.request (PCG_AddressLaws.model_391 program pool))],PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (PCG_AddressLaws.model_391 program pool)))⟩ ∧
 PCG_SdkPda.Domain (PCG_RequestCarrier.request (PCG_AddressLaws.model_391 program pool)) ∧
 (PCG_RequestCarrier.request (PCG_AddressLaws.model_391 program pool)).program = program ∧ (PCG_RequestCarrier.request (PCG_AddressLaws.model_391 program pool)).seeds.val.length = 2 := by
 constructor
 · rw [PCG_AddressLaws.request_391]
   rfl
 · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
   rw [PCG_RequestCarrier.exact_count _ (PCG_AddressLaws.domain_391 program pool).1]
   rfl
#print axioms row_391
end PCG_AddressRoots
