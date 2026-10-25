"""Text-only adaptation of reviewed kernel replay; never invokes Lean."""
import subprocess
from pathlib import Path
D=Path('tools/port30join-20261025')
def blob(rev,path): return subprocess.check_output(['git','show',rev+':'+path]).decode()
s=blob('74a62fd7b6','tools/port29sdkdata-20261025/Port29SDKDATA_Strict-v3.lean')
s=s[:s.index('def readComplete')].replace('namespace Port29SDKDATA','namespace Port30JOIN_Literal')
s=s.replace('private def strictDeclaration','def strictDeclaration')
s+='\nend Port30JOIN_Literal\n'
(D/'Port30JOIN_Literal.lean').write_text('/- Uncompiled Port30JOIN data comparator, copied from immutable Port29 strict-v3. -/\n'+s)
s=blob('904745b496','evidence/port18validate-20261024/lean-002/sources/Port18COHERENCE_Kernel.lean')
s=s.replace('def addDecl (d : Declaration) : M Unit := do', 'def addDecl (d : Declaration) : M Unit := do\n  throw (IO.userError \"Port30JOIN kernel insertion disabled\")')
s=s.replace('import Lean','import Lean\nimport Port30JOIN_Literal').replace('Port18COHERENCE_Kernel','Port30JOIN_Kernel')
a=s.index('          -- Ignore duplicate theorems.')
b=s.index('          addDecl (Declaration.thmDecl',a)
s=s[:a]+s[b:]
s=s.replace('if ! (info == info\') then', 'if !Port30JOIN_Literal.strictDeclaration (.ctorInfo info) (.ctorInfo info\') then',1)
s=s.replace('if ! (info == info\') then', 'if !Port30JOIN_Literal.strictDeclaration (.recInfo info) (.recInfo info\') then',1)
s=s.replace('  return .ofKernelEnv s.env','''  unless s.remaining.isEmpty && s.pending.isEmpty do
    throw (IO.userError "unfinished replay group")
  return .ofKernelEnv s.env''')
s=s.replace('/--\n"Replay" some constants', '''/-- DISABLED candidate interface: caller must establish full exact-name closure,
complete groups and explicit origin policy before enabling this function.
"Replay" some constants''')
s=s.replace('def replay (newConstants', 'private def replayDisabled (newConstants')
s=s.replace('  let mut remaining : NameSet := ∅', '  throw (IO.userError \"Port30JOIN kernel calls disabled pending lead review/allocation\")\n  let mut remaining : NameSet := ∅')
(D/'Port30JOIN_Kernel.lean').write_text(s+'\nend Port30JOIN_Kernel\n')
for n in ['Port18VALIDATE_ATTRIBUTION.md','Port18VALIDATE_LICENSE']:
 (D/n.replace('Port18VALIDATE','Port30JOIN')).write_text(blob('904745b496','docs/research/100bit-spend-path-20261013/lean/'+n))
print('disabled private replay candidate written; no invocation')
