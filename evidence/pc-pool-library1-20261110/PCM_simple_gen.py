from pathlib import Path
E=Path(__file__).resolve().parent
# Source-fixed, allocation-free helpers. Full ProgramError, no ABI quotient.
rows={
308:('Bytes','Unit','if a == [65,83,56,67,1,8,1,0] then .ok () else .error .invalidInstructionData'),
334:('Bytes','Bytes × Hints','if a.length < 4 then .error .invalidInstructionData else\n    let i := a.length - 4\n    .ok (a.take i, ⟨a[i]!,a[i+1]!,a[i+2]!,a[i+3]!⟩)'),
367:('List AccountInfo','Unit','if PCM_POOL_350.duplicateKeys (a.map AccountInfo.key) then .error .invalidArgument else .ok ()'),
382:('List AccountInfo','List AccountInfo','match a with\n  | [mint,source,authority,vault,token] => .ok [source,mint,vault,authority,token]\n  | _ => .error (if a.length < 5 then .notEnoughAccountKeys else .invalidArgument)'),
383:('List AccountInfo','List AccountInfo','match a with\n  | [mint,vault,destination,authority,token] => .ok [vault,mint,destination,authority,token]\n  | _ => .error (if a.length < 5 then .notEnoughAccountKeys else .invalidArgument)')}
for n,(args,ret,ref) in rows.items():
 imports='import PCM_Carriers\n'+('import PCM_Spec_POOL_350\n' if n==367 else '')
 (E/f'PCM_Spec_POOL_{n}.lean').write_text(f'''{imports}set_option autoImplicit false
namespace PCM_POOL_{n}
open RSL PCM
abbrev Args := {args}
def model (a : Args) : Except ProgramError ({ret}) :=
  {ref}
def Ref (a : Args) : Computation ({ret}) := Computation.ofExcept (model a)
def RowSpec (impl : Args → State → Env → Observation ({ret})) : Prop :=
  PCM.RowSpec (fun _ => True) Ref impl
end PCM_POOL_{n}
''')
print('PCM source-small helper specifications emitted')
