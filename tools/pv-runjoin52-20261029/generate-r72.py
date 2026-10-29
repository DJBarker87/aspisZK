exec((__import__('pathlib').Path(__file__).parent/'generate-neutral.py').read_text().split("raw='PV_RunJoin_CircleRawScalar52'")[0])
p=R/'docs/research/100bit-spend-path-20261013/evidence/actual-ten-round-polynomial-run-20261019/focused-dependency-checks/selected-canonical-R72-Funs-20261019/source.lean'
s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'@\[.*?\]\s*','',s,flags=re.S)
s=s[s.index('def core.option.Option.ok_or'):]
s=s[:re.search(r'^def\s+transcript\.',s,re.M).start()]
parts=[p.strip() for p in re.split(r'(?=^def )',s,flags=re.M) if p.strip()];defs={re.match(r'def (\S+)',p)[1]:p for p in parts}
# Transform only the typed projections and constructor labels, leaving variable names unchanged.
def neutral(d):
 d=re.sub(r'\{ a, b \}', '{ fst := a, snd := b }',d)
 d=re.sub(r'\{ c0 := c, c1 \}', '{ fst := c, snd := c1 }',d)
 for a,b in [('a','fst'),('b','snd'),('c0','fst'),('c1','snd'),('x','fst'),('y','snd')]:
  d=re.sub(r'\.'+a+r'\b','.'+b,d);d=re.sub(r'([,{]\s*)'+a+r'\s*:=',lambda m:m[1]+b+' :=',d)
 return d
body='''abbrev field.M31 := U32
abbrev field.CM31 := U32 × U32
abbrev field.QM31 := field.CM31 × field.CM31
abbrev circle.SecureCirclePoint := field.QM31 × field.QM31
abbrev circle.CirclePointError := Bool
def circle.CirclePointError.SingularParameter : Bool := false
def circle.CirclePointError.ParameterInCm31Subfield : Bool := true
abbrev field.r24_canonical_mul.closure := Unit
'''
body+='\n\n'.join(neutral(d) for d in defs.values())
write('PV_RunJoin_CircleR72Raw52',['Aeneas'],body,list(defs))
carrier='''abbrev CM := U32 × U32
abbrev Q := CM × CM
abbrev Point := Q × Q
abbrev OC := AspisR72Sampler.field.CM31
abbrev OQ := AspisR72Sampler.field.QM31
abbrev OP := AspisR72Sampler.circle.SecureCirclePoint
def encCM (a : CM) : OC := ⟨a.1,a.2⟩
def decCM (a : OC) : CM := (a.a,a.b)
def encQ (a : Q) : OQ := ⟨encCM a.1,encCM a.2⟩
def decQ (a : OQ) : Q := (decCM a.c0,decCM a.c1)
def encPoint (a : Point) : OP := ⟨encQ a.1,encQ a.2⟩
def decPoint (a : OP) : Point := (decQ a.x,decQ a.y)
def encError (e : Bool) : AspisR72Sampler.circle.CirclePointError :=
  if e then .ParameterInCm31Subfield else .SingularParameter
def encOutcome (r : core.result.Result Point Bool) :
    core.result.Result OP AspisR72Sampler.circle.CirclePointError :=
  match r with | .Ok p => .Ok (encPoint p) | .Err e => .Err (encError e)
theorem cm_roundtrip (a : CM) : decCM (encCM a)=a := rfl
theorem q_roundtrip (a : Q) : decQ (encQ a)=a := rfl
theorem point_roundtrip (a : Point) : decPoint (encPoint a)=a := rfl
theorem cm_source (a : OC) : encCM (decCM a)=a := rfl
theorem q_source (a : OQ) : encQ (decQ a)=a := rfl
theorem point_source (a : OP) : encPoint (decPoint a)=a := rfl
theorem cm_a (a : CM) : (encCM a).a=a.1 := rfl
theorem cm_b (a : CM) : (encCM a).b=a.2 := rfl
theorem q_c0 (a : Q) : (encQ a).c0=encCM a.1 := rfl
theorem q_c1 (a : Q) : (encQ a).c1=encCM a.2 := rfl
'''
write('PV_RunJoin_CircleR72Carrier52',['AspisR72Sampler.Types'],carrier,re.findall(r'^(?:theorem|def) (\w+)',carrier,re.M))
(E/'r72-neutral-generation.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),functions=list(defs),method='new neutral tuple definitions; selected source unchanged'),indent=2)+'\n')
ops=[n for n in defs if not n.startswith('core.')]
raw='PV_RunJoin_CircleR72Raw52';mods=[]
for i,n in enumerate(ops):
 d=defs[n]; sig=d[:d.index(':=')].removeprefix('def '+n).strip();sep=sig.rfind(':');binder=sig[:sep].strip();result=sig[sep+1:].strip()
 binder=binder.replace('field.M31','U32').replace('field.CM31','CM').replace('field.QM31','Q').replace('field.r24_canonical_mul.closure','Unit')
 args=re.findall(r'\((\w+)\s*:',binder); call=[]
 for a in args:
  typ=re.search(r'\('+a+r'\s*:\s*([^\)]+)\)',binder)[1]
  call.append(f'(encCM {a})' if typ=='CM' else f'(encQ {a})' if typ=='Q' else a)
 const=not result.startswith('Result'); out=result.removeprefix('Result').strip()
 enc='encCM' if out=='field.CM31' else 'encQ' if out=='field.QM31' else '(Option.map encQ)' if out=='(Option field.QM31)' else 'encOutcome' if 'circle.SecureCirclePoint circle.CirclePointError' in out else None
 rhs=raw+'.'+n+' '+' '.join(args)
 if enc: rhs=enc+' ('+rhs+')' if const else '(do let x ← '+rhs+'; ok ('+enc+' x))'
 stmt=f'theorem op{i} {binder} :\n    AspisR72Sampler.{n} '+ ' '.join(call)+' = '+rhs+' := by\n'
 stmt+='  unfold AspisR72Sampler.'+n+' '+raw+'.'+n+'\n'
 deps=['op'+str(j) for j,m in enumerate(ops[:i]) if m in d[len('def '+n):]]
 simp=deps+['cm_a','cm_b','q_c0','q_c1','bind_assoc_eq','bind_tc_ok']
 if deps or args:stmt+='  simp only ['+','.join(simp)+']\n'
 stmt+='  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]\n  all_goals rfl\n'
 stem='PV_RunJoin_CircleR72Op'+str(i)+'52';imports=[mods[-1] if mods else 'PV_RunJoin_CircleR72Carrier52',raw]
 text='\n'.join('import R1Z.'+m for m in imports)+'\nimport AspisR72Sampler.Funs\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.PV_RunJoin_CircleR72Ops52\nopen PV_RunJoin_CircleR72Carrier52\nattribute [local irreducible] encCM encQ\n'+stmt+f'\n#print axioms op{i}\nend R1Z.PV_RunJoin_CircleR72Ops52\n'
 (L/(stem+'.lean')).write_text(text);mods.append(stem)
(E/'r72-op-sequence.json').write_text(json.dumps(mods,indent=2)+'\n')
p=L/'PV_RunJoin_CircleR72Op1652.lean';s=p.read_text();a=s.index(' := by\n');b=s.index('#print axioms')
s=s[:a]+''' := by
  unfold AspisR72Sampler.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.inv
  have hi : AspisR72Sampler.field.M31.inv = PV_RunJoin_CircleR72Raw52.field.M31.inv := funext op15
  rw [hi]
  exact op11 self PV_RunJoin_CircleR72Raw52.field.M31.inv

'''+s[b:];p.write_text(s)
p=L/'PV_RunJoin_CircleR72Op2352.lean';s=p.read_text();a=s.index(' := by\n');b=s.index('#print axioms')
s=s[:a]+''' := by
  unfold AspisR72Sampler.field.QM31.try_inv PV_RunJoin_CircleR72Raw52.field.QM31.try_inv
  rw [op2]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero _
  cases zero with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    simp only [q_c0,q_c1,op19,op7,op22,op16,op20,op21,
      bind_assoc_eq,bind_tc_ok,Option.map_some]
    all_goals simp only [encQ]
    all_goals rfl

'''+s[b:];p.write_text(s)
