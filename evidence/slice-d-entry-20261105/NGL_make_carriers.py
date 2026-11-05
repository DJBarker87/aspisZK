from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
variants=['Custom','InvalidArgument','InvalidInstructionData','InvalidAccountData','AccountDataTooSmall','InsufficientFunds','IncorrectProgramId','MissingRequiredSignature','AccountAlreadyInitialized','UninitializedAccount','NotEnoughAccountKeys','AccountBorrowFailed','MaxSeedLengthExceeded','InvalidSeeds','BorshIoError','AccountNotRentExempt','UnsupportedSysvar','IllegalOwner','MaxAccountsDataAllocationsExceeded','InvalidRealloc','MaxInstructionTraceLengthExceeded','BuiltinProgramsMustConsumeComputeUnits','InvalidAccountOwner','ArithmeticOverflow','Immutable','IncorrectAuthority']
s='import NGJ_VERIFIER_IMPORT\nimport NGL_MetaReference.Types\nimport NGL_MapReference.Types\nset_option autoImplicit false\nnamespace NGL_ErrorCarrier\nopen Aeneas Aeneas.Std Result\nabbrev PE := AdapterRw.solana_program_error.ProgramError\n'
for family,label in [('NGL_MetaReference','meta'),('NGL_MapReference','mapped')]:
 for direction in ['to','from']:
  dom='PE' if direction=='to' else family+'.ProgramError';cod=family+'.ProgramError' if direction=='to' else 'PE'
  s+=f'def {direction}_{label} : {dom} → {cod}\n'
  for v in variants:s+=f'  | .{v}'+(' x' if v in ['Custom','BorshIoError']else'')+f' => .{v}'+(' x'if v in ['Custom','BorshIoError']else'')+'\n'
 s+=f'theorem {label}_left (e : PE) : from_{label} (to_{label} e) = e := by cases e <;> rfl\n'
 s+=f'theorem {label}_right (e : {family}.ProgramError) : to_{label} (from_{label} e) = e := by cases e <;> rfl\n'
 s+=f'#print axioms {label}_left\n#print axioms {label}_right\n'
s+='end NGL_ErrorCarrier\n';(E/'NGL_ErrorCarrier.lean').write_text(s)
(E/'NGL_CARRIER_VARIANTS.json').write_text(json.dumps(dict(variants=variants,count=len(variants),complete=True,fields_preserved=['Custom U32','BorshIoError String']),indent=1)+'\n')
