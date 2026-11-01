"""Prepare new privacy-only modules from hash-selected sources; no build actions."""
from pathlib import Path
import json, hashlib, subprocess
B=Path(__file__).resolve().parent; R=B.parent.parent; D=R/'evidence/pv-dup-20261029'
sources=json.loads((D/'SOURCES-COMPLETED.json').read_text()); changes=[]
def git(p):return subprocess.check_output(['git','show',f'HEAD:{p}'],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
# The adapter changes ONLY the generated instance identifier, not its reader.
original='docs/research/100bit-spend-path-20261013/lean/ImportUnionNamedDiscriminant.lean'
s=git(original).decode().replace('ImportUnionNamedDiscriminant','PV_BR_DiscriminantAdapter').replace('import_union_discriminant','pv_bridge_discriminant').replace('namedDiscriminant','pvBridgeDiscriminant')
(B/'PV_BR_DiscriminantAdapter.lean').write_text(s)
for mod,out in [('R1Z.BuilderAdmissionExtracted','PV_BR_BuilderAdmission'),('AspisR1ProverCommit.Types','PV_BR_ProverTypes')]:
 row=sources[mod]; raw=git(row['source']); assert sha(raw)==row['sha256'],mod
 s=raw.decode().replace('import ImportUnionNamedDiscriminant','import PV_BR_DiscriminantAdapter').replace('import_union_discriminant','pv_bridge_discriminant')
 (B/f'{out}.lean').write_text(s)
 changes.append({'module':out,'source_module':mod,'source':row,'new_sha256':sha(s.encode()),'changes':['import replacement','attribute spelling; generated reader unchanged; enum-qualified instance identifier'], 'status':'UNCOMPILED'})
constructors=[json.loads(l) for l in (D/'lean-70765/stdout.log').read_text().splitlines() if l.startswith('{')]
lines=['import PV_BR_BuilderAdmission','import PV_BR_ProverTypes','import AspisR1WithdrawalValidation.Types','import AspisR1TerminalDecoder.Types','import AspisR1FinishRelationCurrent.Types','', '/-! D540 privacy-only transport. No omission of retry or entropy outcomes. -/','set_option autoImplicit false','namespace PV_BR_Transport']
queries=[]
for label,left,right in [('payment',0,2),('tree',1,3)]:
 a,b=constructors[left],constructors[right]; old=a['type']; new=b['type']; ac=a['constructors']; bc=b['constructors']; assert [x.rsplit('.',1)[1] for x in ac]==[x.rsplit('.',1)[1] for x in bc]
 lines += [f'\nabbrev {label}Shared := {new}',f'def {label}ToShared : {old} → {new}']+[f'  | {x} => {y}' for x,y in zip(ac,bc)]
 lines += [f'def {label}FromShared : {new} → {old}']+[f'  | {y} => {x}' for x,y in zip(ac,bc)]
 for name,ty,expr in [(f'{label}_left_inverse',old,f'{label}FromShared ({label}ToShared e) = e'),(f'{label}_right_inverse',new,f'{label}ToShared ({label}FromShared e) = e')]:
  lines += [f'theorem {name} (e : {ty}) : {expr} := by', '  cases e <;> rfl']; queries.append(name)
 lines += [f'theorem {label}_injective : Function.Injective {label}ToShared := by',f'  intro a b h',f'  have h\' := congrArg {label}FromShared h',f'  exact ({label}_left_inverse a).symm.trans (h\'.trans ({label}_left_inverse b))']; queries.append(f'{label}_injective')
a,b=constructors[4],constructors[5]; small=a['type']; big=b['type']; ac=a['constructors']; bc=b['constructors']; extra=bc[8:]
lines+=['\ninductive ProverOnly where','  | rejected | attemptsExhausted | entropy',f'abbrev VerifierShared := {small}',f'def verifierEmbed : {small} → {big}']+[f'  | {x} => {y}' for x,y in zip(ac,bc)]
lines += [f'def verifierSplit : {big} → Sum {small} ProverOnly']+[f'  | {y} => .inl {x}' for x,y in zip(ac,bc)]+[f'  | {x} => .inr .{y}' for x,y in zip(extra,['rejected','attemptsExhausted','entropy'])]
lines += [f'def verifierJoin : Sum {small} ProverOnly → {big}']+[f'  | .inl {x} => {y}' for x,y in zip(ac,bc)]+[f'  | .inr .{y} => {x}' for x,y in zip(extra,['rejected','attemptsExhausted','entropy'])]
lines += [f'theorem verifier_retraction (e : {small}) : verifierSplit (verifierEmbed e) = .inl e := by','  cases e <;> rfl',f'theorem verifier_join_split (e : {big}) : verifierJoin (verifierSplit e) = e := by','  cases e <;> rfl',f'theorem verifier_split_join (e : Sum {small} ProverOnly) : verifierSplit (verifierJoin e) = e := by','  cases e with','  | inl e => cases e <;> rfl','  | inr e => cases e <;> rfl','theorem verifier_embedding_injective : Function.Injective verifierEmbed := by','  intro a b h','  have h\' := congrArg verifierSplit h','  rw [verifier_retraction, verifier_retraction] at h\'','  exact Sum.inl.inj h\'']
queries += ['verifier_retraction','verifier_join_split','verifier_split_join','verifier_embedding_injective']
lines += ['\n/-- Complete Rust Result error transport, including every error constructor. -/','def mapCoreError {T E F : Type} (f : E → F) :','    Aeneas.Std.core.result.Result T E → Aeneas.Std.core.result.Result T F','  | .Ok x => .Ok x','  | .Err e => .Err (f e)','theorem mapCoreError_inverse {T E F : Type} (f : E → F) (g : F → E)','    (inverse : ∀ e, g (f e) = e) (r : Aeneas.Std.core.result.Result T E) :','    mapCoreError g (mapCoreError f r) = r := by','  cases r with','  | Ok x => rfl','  | Err e => exact congrArg Aeneas.Std.core.result.Result.Err (inverse e)']
queries+=['mapCoreError_inverse']
for label,left in [('payment',0),('tree',1)]:
 ty=constructors[left]['type']; name=f'{label}_result_transport'
 lines += [f'theorem {name} {{T : Type}} (r : Aeneas.Std.core.result.Result T {ty}) :',f'    mapCoreError {label}FromShared (mapCoreError {label}ToShared r) = r :=',f'  mapCoreError_inverse {label}ToShared {label}FromShared {label}_left_inverse r']; queries.append(name)
lines+=['']+[f'#print axioms {q}' for q in queries]+['end PV_BR_Transport','']
(B/'PV_BR_Transport.lean').write_text('\n'.join(lines))
(B/'SOURCE-TRANSFORM.json').write_text(json.dumps({'adapter_source':original,'adapter_source_sha256':sha(git(original)),'transforms':changes,'scope':'Prepared only. No original privacy or Stream A source/object edited. No re-extraction or executable-binding claim.'},indent=2)+'\n')
print('prepared 4 modules; UNCOMPILED')
