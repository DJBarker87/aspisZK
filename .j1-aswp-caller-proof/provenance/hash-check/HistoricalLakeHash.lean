import Lake.Build.Trace

def main (args : List String) : IO Unit := do
  let source := args[0]!
  let object := args[1]!
  let s ← Lake.computeTextFileHash source
  let o ← Lake.computeBinFileHash object
  IO.println s!"source_lake_hash={s}"
  IO.println s!"object_lake_hash={o}"
