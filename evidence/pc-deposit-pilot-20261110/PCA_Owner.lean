import PCA_Event
set_option autoImplicit false
namespace PCA
structure Plan (α : Type) where
  run : Children → PCA_State → Execution α
namespace Plan
def pure {α : Type} (x : α) : Plan α := ⟨fun _ s => ⟨s,[],.ok x⟩⟩
def bind {α β : Type} (p : Plan α) (f : α → Plan β) : Plan β := ⟨fun k s =>
  let r := p.run k s
  match r.reply with
  | .ok x => let q := (f x).run k r.state; ⟨q.state,r.events ++ q.events,q.reply⟩
  | .error e => ⟨r.state,r.events,.error e⟩
  | .abort e => ⟨r.state,r.events,.abort e⟩⟩
instance : Monad Plan where
  pure := pure
  bind := bind
def get : Plan PCA_State := ⟨fun _ s => ⟨s,[],.ok s⟩⟩
def check (site : Nat) (condition : Bool) (error : ProgramError) : Plan Unit :=
  ⟨fun _ s => if condition then ⟨s,[.branch site true],.ok ()⟩
    else ⟨s,[.branch site false,.propagate site error],.error error⟩⟩
def branch (site : Nat) (condition : Bool) : Plan Bool :=
  ⟨fun _ s => ⟨s,[.branch site condition],.ok condition⟩⟩
def call {α : Type} (site : Nat) (c : Call α)
    (map : ProgramError → ProgramError := id) : Plan α := ⟨fun k s =>
  let r := k site c s
  let eventPrefix := [.enter site c s] ++ r.events
  let returning := eventPrefix ++ [.leave site r.reply r.state]
  match r.reply with
  | .error e => ⟨r.state,returning ++ (if map e = e then [] else [.mapError site e (map e)]) ++
      [.propagate site (map e)],.error (map e)⟩
  | .ok x => ⟨r.state,returning,.ok x⟩
  | .abort e => ⟨r.state,eventPrefix,.abort e⟩⟩
def account (site index : Nat) : Plan Nat := ⟨fun _ s =>
  let r : Outcome Nat := if index < s.accountCount then .ok index else .error notEnoughKeys
  ⟨s,[.enter site (.accountGet index) s,.leave site r s] ++
    (if index < s.accountCount then [] else [.propagate site notEnoughKeys]),r⟩⟩
def acquire (site account : Nat) : Plan NLF_RefCell.Guard := ⟨fun _ s =>
  let r := NLF_ParentModel.acquire s.loans account .exclusive
  let s' := {s with loans := r.1}
  let event := PCA_Event.token (.acquire account s.loans.next .exclusive r.2)
  match r.2 with
  | .ok g => ⟨{s' with liveGuards := g :: s.liveGuards},[event],.ok g⟩
  | .error _ => ⟨s',[event,.propagate site borrowFailed],.error borrowFailed⟩⟩
def copy (site : Nat) (g : NLF_RefCell.Guard) (bytes : Bytes) : Plan Unit := ⟨fun _ s =>
  let d := NLF_ParentModel.deref s.loans g
  let s' := {s with loans := d.1}
  let events := [PCA_Event.token (.deref g d.2)]
  match d.2 with
  | .error _ => ⟨s',events,.abort "invalid live exclusive guard"⟩
  | .ok old => if old.bytes.length = bytes.length then
      let payload := {old with bytes := bytes}
      let loans := {s'.loans with state := NLF_ViewLaws.write s'.loans.state g payload}
      ⟨{s' with loans := loans},events ++ [.copy site g bytes],.ok ()⟩
    else ⟨s',events,.abort "copy_from_slice length mismatch"⟩⟩
end Plan

def key (s : PCA_State) (a : Nat) : Bytes := (s.loans.state.accounts a).key
/-- UInt64 little-endian seed bytes, including all eight positions. -/
def le64 (n : UInt64) : Bytes := (List.range 8).map (fun i => UInt8.ofNat (n.toNat / 2^(8*i)))
def pageSeed : Bytes := "aspis-pool-root-page-v1".toUTF8.toList

def selectMode (s : PCA_State) (lane : Lane) (append : Append) : Plan Mode := do
  let current ← Plan.call 1027 (.location lane.tree.nextLeafIndex)
  let next ← Plan.call 1028 (.location append.rootSequence)
  let fresh ← if ← Plan.branch 1029 (lane.tree.nextLeafIndex == 0) then do
      let sys ← Plan.branch 1030 ((s.loans.state.accounts 2).owner == List.replicate 32 0)
      let empty ← if sys then Plan.call 1031 (.empty 2) else pure false
      if empty then pure true else Plan.call 1032 (.zeroed 2 s.programId)
    else pure false
  if ← Plan.branch 1033 fresh then
    let (expected,bump) ← Plan.call 1034 (.pageAddress s.programId (key s 1) 0)
    let preparation ← Plan.call 1035 (.freshPda 2 s.programId expected 8256)
    pure (.fresh preparation bump)
  else if ← Plan.branch 1046 (next.pageNumber == current.pageNumber) then
    let header ← Plan.call 1048 (.currentPage s.programId 1 2 lane true none)
    pure (.same header)
  else
    let header ← Plan.call 1056 (.currentPage s.programId 1 2 lane false none)
    Plan.check 1057 (header.filled.toNat == 256) historyMismatch
    let page ← Plan.account 1060 3
    let (expected,bump) ← Plan.call 1062 (.pageAddress s.programId (key s 1) next.pageNumber)
    let preparation ← Plan.call 1063 (.freshPda page s.programId expected 8256)
    pure (.rollover preparation next.pageNumber bump)

def preparePage (s : PCA_State) (mode : Mode) : Plan Nat := do
  match mode with
  | .same _ => pure 2
  | .fresh preparation bump =>
    Plan.call 1097 (.payerSystem 8 9)
    if ← Plan.branch 1098 (preparation == .createOrAllocate) then
      Plan.call 1107 (.createPda 8 2 9 8256 s.programId
        [pageSeed,key s 1,le64 0,[bump]])
    Plan.call 1117 (.ownedZeroed 2 s.programId 8256 s.rent)
    pure 2
  | .rollover preparation page bump =>
    Plan.call 1135 (.payerSystem 9 10)
    if ← Plan.branch 1136 (preparation == .createOrAllocate) then
      Plan.call 1145 (.createPda 9 3 10 8256 s.programId
        [pageSeed,key s 1,le64 page,[bump]])
    Plan.call 1155 (.ownedZeroed 3 s.programId 8256 s.rent)
    pure 3

/-- Complete source-ordered parent, frozen pair_forest.rs:988–1196.
Intermediate only: k must ultimately be instantiated from CLOSED child roots.
It is intentionally not a POOL:328 root or a claim of native association. -/
def deposit : Plan Unit := do
  let s ← Plan.get
  let request ← Plan.call 995 (.decode s.instructionData) (fun _ => invalidInstruction)
  let masterAccount ← Plan.account 997 0
  let laneAccount ← Plan.account 1000 1
  let _currentPage ← Plan.account 1003 2
  let master ← Plan.call 1006 (.master s.programId masterAccount)
  let commitment ← Plan.call 1007 (.commitment request.ownerKey request.amount master.identity.assetId request.salt)
  let laneId ← Plan.call 1013 (.laneId commitment) (fun _ => nonCanonicalLeaf)
  Plan.check 1015 (decide (master.initializedLaneMask.toNat / 2^laneId.toNat % 2 ≠ 0)) historyMismatch
  let lane ← Plan.call 1018 (.lane s.programId (key s masterAccount) laneId laneAccount)
  Plan.check 1019 (decide (lane.tree.nextLeafIndex.toNat < 2^20)) treeFull
  let witness ← Plan.call 1022 (.singleOutput commitment) (fun _ => nonCanonicalLeaf)
  let leaf ← Plan.call 1023 (.leafDigest witness) (fun _ => nonCanonicalLeaf)
  let (append,image) ← Plan.call 1025 (.prepare lane laneId leaf)
  let mode ← selectMode s lane append
  let tokenStart := match mode with | .rollover .. => 4 | _ => 3
  let count := match mode with | .fresh .. => 10 | .same .. => 8 | .rollover .. => 11
  Plan.call 1080 (.exactCount count)
  Plan.call 1081 .unique
  let tokenAccounts := (List.range 5).map (tokenStart + ·)
  Plan.call 1083 (.tokenProgram (tokenStart+4))
  let transfer ← Plan.call 1084 (.transfer s.programId (key s masterAccount) master.identity tokenAccounts request.amount)
  let infos ← Plan.call 1091 (.transferInfos tokenAccounts)
  let page ← preparePage s mode
  let laneGuard ← Plan.acquire 1168 laneAccount
  let pageGuard ← Plan.acquire 1169 page
  Plan.call 1170 (.invoke transfer.instruction infos)
  Plan.call 1171 (.delta tokenAccounts transfer)
  Plan.copy 1173 laneGuard image.toList
  match mode with
  | .fresh .. => Plan.call 1175 (.writePage pageGuard (key s laneAccount) 0 0 [lane.tree.root,append.root])
  | .same header => Plan.call 1183 (.appendRoots pageGuard header [append.root])
  | .rollover _ page _ => Plan.call 1187 (.writePage pageGuard (key s laneAccount) page append.rootSequence [append.root])
  pure ()

/-- Lexical reverse order: page then lane. On an abort there is NO cleanup.
Returning child errors have already released the child's own guards. -/
def cleanup : List NLF_RefCell.Guard → PCA_State → PCA_State × List PCA_Event
  | [], s => ({s with liveGuards := []},[])
  | g::gs, s =>
    let r := NLF_ParentModel.release s.loans g
    let q := cleanup gs {s with loans := r.1, liveGuards := gs}
    (q.1,PCA_Event.token (.release g r.2) :: q.2)

def finish (r : Execution Unit) : Execution Unit :=
  match r.reply with
  | .abort reason => {r with state := {r.state with returned := some r.reply}, events := r.events ++ [.aborted reason]}
  | _ => let c := cleanup r.state.liveGuards r.state
         ⟨{c.1 with returned := some r.reply},r.events ++ c.2 ++ [.returned r.reply],r.reply⟩

namespace PCA_Owner
/-- A complete Result/log/post-state specification RELATIVE to typed children.
The runtime is nondeterministic; k selects its replies and unconstrained passed
cell mutations. No root can take this dictionary or the candidate frame. -/
def spec (k : Children) (s : PCA_State) : Execution Unit := finish (deposit.run k s)
end PCA_Owner
end PCA
