import Lean
open Lean
def lits : List Nat := [1455, 1454, 1427, 1426, 815, 787, 1320, 1456, 1428]
def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"
def watched (c : Name) : Bool :=
  let s := c.toString
  (`R0P.Public).isPrefixOf c || ["SemanticPublic","PublicByteCodec","PublicCodecAgreement","PublicOptionShape","SpendRelation.Rspend","LiteralProtocol.relation","runDecodedPublic","RawRecordedPublicSpendExtractor","GSByteJointSpendExtractor"].any (fun k => (s.splitOn k).length > 1)
def refs (e : Expr) : Array String :=
  (e.foldConsts ({} : NameSet) (fun c s => if watched c then s.insert c else s)).toList.toArray.map toString
def litsIn (e : Expr) : Array String := Id.run do
  let mut r := #[]
  for n in lits do
    if (e.find? (fun x => match x with | .lit (.natVal k) => k == n | _ => false)).isSome then r := r.push (toString n)
  return r
unsafe def main (args : List String) : IO Unit := do
  let root := args[0]!
  let lst ← IO.FS.lines args[1]!
  let out ← IO.FS.Handle.mk args[2]! .write
  for m in lst do
    let (md, reg) ← readModuleData (root ++ "/" ++ (m.replace "." "/") ++ ".olean")
    for ci in md.constants do
      let tr := refs ci.type
      let tl := litsIn ci.type
      let (vr, vl) := match ci.value? (allowOpaque := true) with
        | some v => (refs v, litsIn v) | none => (#[], #[])
      if tr.size + tl.size + vr.size + vl.size > 0 then
        out.putStrLn (m ++ "\t" ++ ci.name.toString ++ "\t" ++ kindOf ci ++ "\t" ++ String.intercalate " " tr.toList ++ "\t" ++ String.intercalate " " tl.toList ++ "\t" ++ String.intercalate " " vr.toList ++ "\t" ++ String.intercalate " " vl.toList)
    reg.free
