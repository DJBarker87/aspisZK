import JGw_Tree2
-- Missing evidence artifact: inspect the actually imported cohort, including
-- nested repository modules and external toolchain/library modules.
run_cmd do
  let env ← Lean.getEnv
  for modName in env.header.moduleNames do
    let path ← Lean.findOLean modName
    for suffix in ["", ".server", ".private"] do
      let artifact := System.FilePath.mk (path.toString++suffix)
      if ← artifact.pathExists then
        let metadata ← artifact.metadata
        Lean.logInfo m!"JGy_OBJECT\t{modName}\t{artifact}\t{metadata.byteSize}"
