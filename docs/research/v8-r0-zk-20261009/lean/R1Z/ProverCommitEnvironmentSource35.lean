import AspisR1Environment35.Funs
import R1Z.ProverCommitEnvironment35
/-! The extracted structural reservation owner is connected to the D147
schedule for every history and payload-blind schedule. The external Kani gate
connects the native source control to this same Rust owner; OS primitives,
path computation and byte storage remain explicitly external boundaries. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEnvironmentSource35
open Aeneas Aeneas.Std Result AspisR1Environment35 ProverCommitEnvironment35
open R0Z.FsStatement

def kind : owner.Kind → Kind
  | .Create => .create
  | .WriteMagic => .writeMagic
  | .WriteDigest => .writeDigest
  | .WriteNonce => .writeNonce
  | .FileSync => .fileSync
  | .DirectoryOpen => .directoryOpen
  | .DirectorySync => .directorySync

def encodeOutcome : Outcome → core.result.Result Unit IOError
  | .ok _ => .Ok ()
  | .error e => .Err e

def ops (schedule : Schedule) (nonce : OracleAnswer) : owner.IO Unit State IOError where
  call k s :=
    let step := ask schedule (kind k) s
    let after := match k,step.1 with
      | .Create,.ok _ => {step.2 with burned := nonce :: step.2.burned}
      | _,_ => step.2
    ok (encodeOutcome step.1,after)
  duplicate e := ok (match e with | .alreadyExists => true | .other _ => false)

def packChain (result : Outcome × State) : owner.Run State IOError :=
  ⟨match result.1 with | .ok _ => .Ok () | .error e => .Err (.Io e),result.2,true⟩

/-- The finite suffix contains exactly three writes, file sync and, on Unix,
open-directory and directory sync. No suffix is evaluated after an error. -/
theorem finish_source (schedule : Schedule) (nonce : OracleAnswer)
    (unix : Bool) (s : State) :
    owner.finish (ops schedule nonce) 0#u8 unix s =
      ok (packChain (ioChain schedule (writes unix) s)) := by
  have c0 : ∀ state, (ops schedule nonce).call .WriteMagic state =
      ok (encodeOutcome (ask schedule .writeMagic state).1,(ask schedule .writeMagic state).2) := fun _ => rfl
  have c1 : ∀ state, (ops schedule nonce).call .WriteDigest state =
      ok (encodeOutcome (ask schedule .writeDigest state).1,(ask schedule .writeDigest state).2) := fun _ => rfl
  have c2 : ∀ state, (ops schedule nonce).call .WriteNonce state =
      ok (encodeOutcome (ask schedule .writeNonce state).1,(ask schedule .writeNonce state).2) := fun _ => rfl
  have c3 : ∀ state, (ops schedule nonce).call .FileSync state =
      ok (encodeOutcome (ask schedule .fileSync state).1,(ask schedule .fileSync state).2) := fun _ => rfl
  have c4 : ∀ state, (ops schedule nonce).call .DirectoryOpen state =
      ok (encodeOutcome (ask schedule .directoryOpen state).1,(ask schedule .directoryOpen state).2) := fun _ => rfl
  have c5 : ∀ state, (ops schedule nonce).call .DirectorySync state =
      ok (encodeOutcome (ask schedule .directorySync state).1,(ask schedule .directorySync state).2) := fun _ => rfl
  have a0 : U8.wrapping_add 0#u8 1#u8 = 1#u8 := by rfl
  have a1 : U8.wrapping_add 1#u8 1#u8 = 2#u8 := by rfl
  have a2 : U8.wrapping_add 2#u8 1#u8 = 3#u8 := by rfl
  have a3 : U8.wrapping_add 3#u8 1#u8 = 4#u8 := by rfl
  have a4 : U8.wrapping_add 4#u8 1#u8 = 5#u8 := by rfl
  have a5 : U8.wrapping_add 5#u8 1#u8 = 6#u8 := by rfl
  have n01 : (0#u8) ≠ 1#u8 := by decide
  have n02 : (0#u8) ≠ 2#u8 := by decide
  have n03 : (0#u8) ≠ 3#u8 := by decide
  have n04 : (0#u8) ≠ 4#u8 := by decide
  have n05 : (0#u8) ≠ 5#u8 := by decide
  have n10 : (1#u8) ≠ 0#u8 := by decide
  have n12 : (1#u8) ≠ 2#u8 := by decide
  have n13 : (1#u8) ≠ 3#u8 := by decide
  have n14 : (1#u8) ≠ 4#u8 := by decide
  have n15 : (1#u8) ≠ 5#u8 := by decide
  have n20 : (2#u8) ≠ 0#u8 := by decide
  have n21 : (2#u8) ≠ 1#u8 := by decide
  have n23 : (2#u8) ≠ 3#u8 := by decide
  have n24 : (2#u8) ≠ 4#u8 := by decide
  have n25 : (2#u8) ≠ 5#u8 := by decide
  have n30 : (3#u8) ≠ 0#u8 := by decide
  have n31 : (3#u8) ≠ 1#u8 := by decide
  have n32 : (3#u8) ≠ 2#u8 := by decide
  have n34 : (3#u8) ≠ 4#u8 := by decide
  have n35 : (3#u8) ≠ 5#u8 := by decide
  have n40 : (4#u8) ≠ 0#u8 := by decide
  have n41 : (4#u8) ≠ 1#u8 := by decide
  have n42 : (4#u8) ≠ 2#u8 := by decide
  have n43 : (4#u8) ≠ 3#u8 := by decide
  have n45 : (4#u8) ≠ 5#u8 := by decide
  have n50 : (5#u8) ≠ 0#u8 := by decide
  have n51 : (5#u8) ≠ 1#u8 := by decide
  have n52 : (5#u8) ≠ 2#u8 := by decide
  have n53 : (5#u8) ≠ 3#u8 := by decide
  have n54 : (5#u8) ≠ 4#u8 := by decide
  have n60 : (6#u8) ≠ 0#u8 := by decide
  have n61 : (6#u8) ≠ 1#u8 := by decide
  have n62 : (6#u8) ≠ 2#u8 := by decide
  have n63 : (6#u8) ≠ 3#u8 := by decide
  have n64 : (6#u8) ≠ 4#u8 := by decide
  have n65 : (6#u8) ≠ 5#u8 := by decide
  have h6 : ∀ state, owner.finish (ops schedule nonce) 6#u8 unix state =
      ok (packChain (ioChain schedule [] state)) := by
    intro state; rw [owner.finish]
    simp only [n60,n61,n62,n63,n64,n65,if_false,if_true]
    rfl
  have h5 : ∀ state, owner.finish (ops schedule nonce) 5#u8 unix state =
      ok (packChain (ioChain schedule ([.directorySync]) state)) := by
    intro state
    rw [owner.finish]
    simp only [n50,n51,n52,n53,n54,if_false,if_true]
    cases hs : (ask schedule .directorySync state).1 <;>
      simp [c5,hs,encodeOutcome,bind_tc_ok,lift,a5,h6,ioChain,packChain]
  have h4 : ∀ state, owner.finish (ops schedule nonce) 4#u8 unix state =
      ok (packChain (ioChain schedule ([] ++ (if unix then [.directoryOpen,.directorySync] else [])) state)) := by
    intro state
    rw [owner.finish]
    simp only [n40,n41,n42,n43,if_false,if_true]
    cases unix <;> simp only [Bool.false_eq_true,if_false,if_true,List.nil_append]
    · rfl
    ·
      cases hs : (ask schedule .directoryOpen state).1 <;>
        simp [c4,hs,encodeOutcome,bind_tc_ok,lift,a4,h5,ioChain,packChain]
  have h3 : ∀ state, owner.finish (ops schedule nonce) 3#u8 unix state =
      ok (packChain (ioChain schedule ([.fileSync] ++ (if unix then [.directoryOpen,.directorySync] else [])) state)) := by
    intro state
    rw [owner.finish]
    simp only [n30,n31,n32,if_false,if_true]
    cases hs : (ask schedule .fileSync state).1 <;>
      simp [c3,hs,encodeOutcome,bind_tc_ok,lift,a3,h4,ioChain,packChain]
  have h2 : ∀ state, owner.finish (ops schedule nonce) 2#u8 unix state =
      ok (packChain (ioChain schedule ([.writeNonce,.fileSync] ++ (if unix then [.directoryOpen,.directorySync] else [])) state)) := by
    intro state
    rw [owner.finish]
    simp only [n20,n21,if_false,if_true]
    cases hs : (ask schedule .writeNonce state).1 <;>
      simp [c2,hs,encodeOutcome,bind_tc_ok,lift,a2,h3,ioChain,packChain]
  have h1 : ∀ state, owner.finish (ops schedule nonce) 1#u8 unix state =
      ok (packChain (ioChain schedule ([.writeDigest,.writeNonce,.fileSync] ++ (if unix then [.directoryOpen,.directorySync] else [])) state)) := by
    intro state
    rw [owner.finish]
    simp only [n10,if_false,if_true]
    cases hs : (ask schedule .writeDigest state).1 <;>
      simp [c1,hs,encodeOutcome,bind_tc_ok,lift,a1,h2,ioChain,packChain]
  have h0 : ∀ state, owner.finish (ops schedule nonce) 0#u8 unix state =
      ok (packChain (ioChain schedule ([.writeMagic,.writeDigest,.writeNonce,.fileSync] ++ (if unix then [.directoryOpen,.directorySync] else [])) state)) := by
    intro state
    rw [owner.finish]
    simp only [if_false,if_true]
    cases hs : (ask schedule .writeMagic state).1 <;>
      simp [c0,hs,encodeOutcome,bind_tc_ok,lift,a0,h1,ioChain,packChain]
  exact h0 s

def decodeError : owner.Error IOError → ReservationError
  | .Duplicate => .duplicate
  | .Io e => .io e

def unpack (out : owner.Run State IOError) : Except ReservationError Unit × State :=
  (match out.result with | .Ok _ => .ok () | .Err e => .error (decodeError e),out.state)

theorem unpack_chain (out : Outcome × State) :
    unpack (packChain out) = (out.1.mapError ReservationError.io,out.2) := by
  rcases out with ⟨status,s⟩
  cases status <;> rfl

/-- Complete extracted entry point: duplicate errors, all IO errors, successful
reservation and the entire retained ledger/history state agree exactly. -/
theorem reserve_source (schedule : Schedule) (nonce : OracleAnswer)
    (unix : Bool) (s : State) :
    (do let out ← owner.reserve (ops schedule nonce) unix s
        ok (unpack out)) = ok (reserve schedule unix nonce s) := by
  have call : (ops schedule nonce).call .Create s =
      ok (encodeOutcome (ask schedule .create s).1,
        match (ask schedule .create s).1 with
        | .ok _ => {(ask schedule .create s).2 with burned := nonce :: s.burned}
        | .error _ => (ask schedule .create s).2) := by
    cases h : (ask schedule .create s).1 <;> simp [ops,kind,h] <;> rfl
  rw [owner.reserve]
  simp only [call,bind_tc_ok]
  cases h : (ask schedule .create s).1 with
  | error e =>
    cases e <;> simp [h,encodeOutcome,bind_tc_ok,unpack,decodeError,reserve,ops]
  | ok u =>
    cases u
    simp only [h,encodeOutcome,bind_tc_ok]
    change (do let out ← owner.finish (ops schedule nonce) 0#u8 unix _
               ok (unpack out)) = _
    rw [finish_source]
    simp only [bind_tc_ok,unpack_chain,reserve,h] <;> rfl

#print axioms finish_source
#print axioms unpack_chain
#print axioms reserve_source
end R1Z.ProverCommitEnvironmentSource35
