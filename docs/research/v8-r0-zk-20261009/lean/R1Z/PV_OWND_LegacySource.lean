import R1Z.PV_OWNC_LinkPush
set_option autoImplicit false
namespace R1Z.PV_OWND_LegacySource
open PV_OWN_Link
/-- Full source values: no projection erases kind or its payload. -/
def link (kind : Kind) (producer consumer : Nat) : Link :=
 ⟨kind,UInt16.ofNat producer,UInt16.ofNat consumer⟩
def aux (level : Nat) : Nat := 864+(level/4)*16+1+2*(level%4)
def pathBase (level : Nat) : Option Nat := if level<21 then some (aux level) else none
def spongePairs : List (Nat × Nat) := [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]
def sponge : List Link := spongePairs.map fun (f,t) =>
 link (.spongeCarry (UInt8.ofNat f) (UInt8.ofNat t)) (f*16+11) (t*16)
def head : List Link := [link .ownerOutput 11 28,link .nullifierKey 12 412,
 link .inputSaltHead 44 428,link .inputSaltTail 60 428]
def privateLevel (level : Nat) : List Link :=
 [link (.privatePathCurrent (UInt8.ofNat level)) ((3+level)*16+11) (aux level),
  link (.privatePathLeft (UInt8.ofNat level)) (aux level+1) ((4+level)*16+12),
  link (.privatePathRight (UInt8.ofNat level)) (aux level+1) ((4+level)*16)]
def privateLinks : List Link := (List.range 21).flatMap privateLevel
def valueSources : List Link := [(0,44,960),(1,460,962),(2,508,964)].map
 fun (v,p,c) => link (.valueSource (UInt8.ofNat v)) p c
def conservation : List Link := [link .conservationInput 960 966,
 link .conservationRecipient 962 966,link .conservationChange 964 967,
 link .conservationPartial 966 967]
def occupancy : List Link := [link .inputSecondCommitment 64 969,
 link .inputSelectedSide (aux 0) 969,link .outputSecondCommitment (32*16+11) 970,
 link .outputPairFirst (29*16+11) (33*16+12),
 link .outputPairFirstWithdrawal (32*16+11) (33*16+12),link .outputPairSecond 970 (33*16)]
def appendLevel (level : Nat) : List Link :=
 [link (.appendCurrentLeft (UInt8.ofNat level)) ((33+level)*16+11) ((34+level)*16+12),
  link (.appendCurrentRight (UInt8.ofNat level)) ((33+level)*16+11) ((34+level)*16)]
def appendLinks : List Link := (List.range 20).flatMap appendLevel
def phases : List (List Link) := [sponge,head,privateLinks,valueSources,conservation,occupancy,appendLinks]
def links : List Link := phases.flatten
attribute [local irreducible] link aux pathBase spongePairs sponge head privateLevel privateLinks
 valueSources conservation occupancy appendLevel appendLinks phases links
end R1Z.PV_OWND_LegacySource
