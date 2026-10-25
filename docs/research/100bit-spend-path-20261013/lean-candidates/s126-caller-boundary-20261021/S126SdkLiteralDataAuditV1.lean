import S126SdkLiteralComparisonV1
open Lean AspisS126SdkLiteral
namespace AspisS126SdkLiteralDataAudit
def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data



def comparison (a b : ConstantInfo) : Json :=
  Json.mkObj [("alpha_metadata",toJson (sameDeclarationAlphaMetadata a b)),
    ("literal",toJson (sameDeclarationLiteral a b)),
    ("type_alpha",toJson (a.type == b.type)),("type_literal",toJson (Expr.equal a.type b.type)),
    ("value_alpha",toJson (a.value? (allowOpaque := true) == b.value? (allowOpaque := true))),
    ("value_literal",toJson (sameExprOption (a.value? (allowOpaque := true)) (b.value? (allowOpaque := true)))),
    ("recursor_rhs_literal",toJson (sameRecursorRhs a b)),
    ("both_theorems",toJson (a.isTheorem && b.isTheorem))]

def audit : IO Unit := do
  let some inputPath ← IO.getEnv "S126_SDK_LITERAL_INPUT" | throw (IO.userError "missing input")
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile inputPath))
  let transports ← IO.ofExcept (config.getObjValAs? (Array Json) "transports")
  let mut current : Std.HashMap Name ConstantInfo := {}
  let mut currentOwners : Std.HashMap Name String := {}
  let mut duplicates := 0
  let mut alphaDup := 0
  let mut literalDup := 0
  for row in transports do
    let path ← IO.ofExcept (row.getObjValAs? String "path")
    let data ← readComplete path
    unless data.imports.isEmpty && data.extraConstNames.isEmpty && data.entries.isEmpty &&
        data.constNames == data.constants.map (·.name) do
      throw (IO.userError "raw transport structure changed")
    for c in data.constants do
      if let some prior := current[c.name]? then
        duplicates := duplicates+1
        if sameDeclarationAlphaMetadata prior c then alphaDup := alphaDup+1
        if sameDeclarationLiteral prior c then literalDup := literalDup+1
        IO.println ("CURRENT_DUP " ++ (Json.mkObj [("name",toJson c.name.toString),
          ("old_path",toJson currentOwners[c.name]!), ("new_path",toJson path),
          ("comparison",comparison prior c)]).compress)
      else
        current := current.insert c.name c
        currentOwners := currentOwners.insert c.name path
  let factorRows ← IO.ofExcept (config.getObjValAs? (Array Json) "factor_rows")
  let mut originals : Std.HashMap Name ConstantInfo := {}
  let mut factors : Array ConstantInfo := #[]
  let mut originalDuplicates := 0
  let mut originalLiteralDuplicates := 0
  for row in factorRows do
    let path ← IO.ofExcept (row.getObjValAs? String "path")
    let factored ← IO.ofExcept (row.getObjValAs? Bool "factored")
    let data ← readComplete path
    for c in data.constants do
      if factored then factors := factors.push c
      else if let some prior := originals[c.name]? then
        originalDuplicates := originalDuplicates+1
        if sameDeclarationLiteral prior c then originalLiteralDuplicates := originalLiteralDuplicates+1
        IO.println ("FACTOR_INPUT_DUP " ++ (Json.mkObj [("name",toJson c.name.toString),
          ("comparison",comparison prior c)]).compress)
      else originals := originals.insert c.name c
  let mut paired := 0
  let mut factorAlpha := 0
  let mut factorLiteral := 0
  let mut factorTypeAlpha := 0
  let mut factorTypeLiteral := 0
  let mut missing := 0
  for c in factors do
    if let some prior := originals[c.name]? then
      paired := paired+1
      if sameDeclarationAlphaMetadata prior c then factorAlpha := factorAlpha+1
      if sameDeclarationLiteral prior c then factorLiteral := factorLiteral+1
      if prior.type == c.type then factorTypeAlpha := factorTypeAlpha+1
      if Expr.equal prior.type c.type then factorTypeLiteral := factorTypeLiteral+1
      IO.println ("FACTOR " ++ (Json.mkObj [("name",toJson c.name.toString),
        ("comparison",comparison prior c)]).compress)
    else
      missing := missing+1
      IO.println ("FACTOR_MISSING " ++ (toJson c.name.toString).compress)
  let refreshRows ← IO.ofExcept (config.getObjValAs? (Array Json) "proof_refresh")
  let mut refreshCount := 0
  let mut refreshTypeAlpha := 0
  let mut refreshTypeLiteral := 0
  for row in refreshRows do
    let oldPath ← IO.ofExcept (row.getObjValAs? String "old")
    let newPath ← IO.ofExcept (row.getObjValAs? String "new")
    let names ← IO.ofExcept (row.getObjValAs? (Array String) "names")
    let old ← readComplete oldPath
    let fresh ← readComplete newPath
    for n in names do
      -- These six public seed names have no numeric or escaped components.
      let some a := old.constants.find? (fun c => c.name == n.toName) | throw (IO.userError s!"missing old {n}")
      let some b := fresh.constants.find? (fun c => c.name == n.toName) | throw (IO.userError s!"missing new {n}")
      refreshCount := refreshCount+1
      if a.type == b.type then refreshTypeAlpha := refreshTypeAlpha+1
      if Expr.equal a.type b.type then refreshTypeLiteral := refreshTypeLiteral+1
      IO.println ("REFRESH " ++ (Json.mkObj [("name",toJson n),("comparison",comparison a b)]).compress)
  IO.println ("LITERAL_SUMMARY " ++ (Json.mkObj [("current_constants",toJson current.size),
    ("current_duplicates",toJson duplicates),("current_alpha_duplicates",toJson alphaDup),
    ("current_literal_duplicates",toJson literalDup),
    ("factor_paired",toJson paired),("factor_alpha",toJson factorAlpha),("factor_literal",toJson factorLiteral),
    ("factor_type_alpha",toJson factorTypeAlpha),("factor_type_literal",toJson factorTypeLiteral),
    ("factor_missing",toJson missing),("factor_input_duplicates",toJson originalDuplicates),
    ("factor_input_literal_duplicates",toJson originalLiteralDuplicates),
    ("refresh_count",toJson refreshCount),("refresh_type_alpha",toJson refreshTypeAlpha),
    ("refresh_type_literal",toJson refreshTypeLiteral)]).compress)
#eval audit

end AspisS126SdkLiteralDataAudit
