from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
p='docs/research/100bit-spend-path-20261013/lean/extracted-adapter-reconstruct-20261016/AspisR1AdapterReconstruct/Types.lean'
src=subprocess.check_output(['git','show','HEAD:'+p],text=True)
blocks={m[1]:m[2] for m in re.finditer(r'^inductive (aspis_statement\.[\w.]+)\s+where\n(.*?)(?=\n/--|\Z)',src,re.M|re.S)}
root='aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1';needed=[];done=set();parsed={}
def visit(n):
 if n in done:return
 done.add(n);cs=[]
 for m in re.finditer(r'^\| (\w+)\s*:\s*(.*?)(?=\n\||\Z)',blocks[n],re.M|re.S):
  ts=[x.strip() for x in m[2].split('→')];assert ts[-1]==n,(n,ts)
  args=ts[:-1];assert len(args)<=1,(n,args)
  if args:visit(args[0])
  cs.append((m[1],args))
 parsed[n]=cs;needed.append(n)
visit(root)
lines=['import NBN_U05','import JHf_ReconstructionSlot','set_option autoImplicit false','namespace NED_ErrorCarriers','open Aeneas Aeneas.Std Result']
for n in needed:
 short=n.split('.')[-1];raw='AspisR1AdapterReconstruct.'+n;term='AspisR1TerminalDecoder.'+n.removeprefix('aspis_statement.')
 for direction,dom,cod in [('fromRaw',raw,term),('toRaw',term,raw)]:
  lines += [f'def {direction}{short} (value : {dom}) : {cod} :=', '  match value with']
  for constructor,args in parsed[n]:
   if args:lines.append(f'  | .{constructor} x => .{constructor} ({direction}{args[0].split(".")[-1]} x)')
   else:lines.append(f'  | .{constructor} => .{constructor}')
 for name,domain,first,second in [('from_to',term,'toRaw','fromRaw'),('to_from',raw,'fromRaw','toRaw')]:
  lem=f'{name}_{short}'
  lowers=[f'{name}_{a[0].split(".")[-1]}' for _,a in parsed[n] if a]
  lines += [f'theorem {lem} (value : {domain}) :',f'    {second}{short} ({first}{short} value) = value := by',f'  cases value <;> simp only [{first}{short},{second}{short}'+(' ,'+','.join(sorted(set(lowers))) if lowers else '')+']',f'#print axioms {lem}']
lines+=['end NED_ErrorCarriers']
(E/'NED_ErrorCarriers.lean').write_text('\n'.join(lines)+'\n')
(E/'NED_ERROR_CARRIER_SOURCE.json').write_text(json.dumps(dict(source=p,sha256=hashlib.sha256(src.encode()).hexdigest(),enums=needed),indent=1)+'\n')
print('generated',len(needed),'exact error-carrier bijections')
