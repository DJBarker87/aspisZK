//! Literal-state certificates for the R37 restricted-polynomial witness.
include!("r37_residual_arithmetic.rs");
fn advance(p:&[K;27],root:K)->[K;27]{std::array::from_fn(|r|(0..27).fold(K::ZERO,|s,j|s.add(p[j].mul(xentry(j,r)))).sub(root.mul(p[r])))}
fn residues(p:&[K;27])->Vec<u32>{p.iter().map(|v|{let mut b=[0;16];v.write_le_bytes(&mut b);assert_eq!(&b[4..],&[0;12]);u32::from_le_bytes(b[..4].try_into().unwrap())}).collect()}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);assert!(args[1]=="--write"||args[1]=="--check");let out=std::path::Path::new(&args[2]);let checking=args[1]=="--check";
    if !checking{assert!(!out.exists());std::fs::create_dir(out).unwrap();}
    let mut p=[K::ZERO;27];p[0]=K::ONE;let mut roots=vec![p];let mut source_checks=0;
    for r in 1..23{let root=K::ONE.mul_m31(M31(r));let next=advance(&p,root);let source=times_x(&p);assert_eq!(source[27],K::ZERO);for j in 0..27{assert_eq!(next[j],source[j].sub(root.mul(p[j])));source_checks+=1;}p=next;roots.push(p);}
    let mut shifts=vec![p];for _ in 0..4{let next=advance(&p,K::ZERO);let source=times_x(&p);assert_eq!(source[27],K::ZERO);assert_eq!(next.as_slice(),&source[..27]);source_checks+=27;p=next;shifts.push(p);}
    let mut files=std::collections::BTreeMap::<String,String>::new();let header="/- Generated one-step certificate. Do not unfold the full root recurrence. -/\n";
    let mut data=format!("{header}import AspisV8R19.RootCertificate\nimport Mathlib.Tactic.FinCases\nnamespace AspisR19.WitnessRootData\nopen RootCertificate\nnoncomputable section\n");
    for(i,p)in roots.iter().enumerate(){data+=&format!("def p{i} : Fin 27 → M := vector {:?}\n",residues(p));}
    data+="def s0 : Fin 27 → M := p22\n";for(i,p)in shifts.iter().enumerate().skip(1){data+=&format!("def s{i} : Fin 27 → M := vector {:?}\n",residues(p));}data+="end\nend AspisR19.WitnessRootData\n";files.insert("WitnessRootData.lean".into(),data);
    for i in 0..22{let name=format!("WitnessRootStep{:02}",i+1);files.insert(name.clone()+".lean",format!("{header}import AspisV8R19.WitnessRootData\nnamespace AspisR19.WitnessRootData\nopen RootCertificate ResidualModel\ntheorem rootStep{:02} : (fun j => shift half 1 p{i} j-({}:M)*p{i} j)=p{} := by\n  funext j\n  fin_cases j <;> decide\n#print axioms rootStep{:02}\nend AspisR19.WitnessRootData\n",i+1,i+1,i+1,i+1));}
    for i in 0..4{let name=format!("WitnessShiftStep{}",i+1);files.insert(name.clone()+".lean",format!("{header}import AspisV8R19.WitnessRootData\nnamespace AspisR19.WitnessRootData\nopen RootCertificate ResidualModel\ntheorem shiftStep{} : shift half 1 s{i}=s{} := by\n  funext j\n  fin_cases j <;> decide\n#print axioms shiftStep{}\nend AspisR19.WitnessRootData\n",i+1,i+1,i+1));}
    let mut bridge=String::from(header);for i in 1..23{bridge+=&format!("import AspisV8R19.WitnessRootStep{i:02}\n");}for i in 1..5{bridge+=&format!("import AspisV8R19.WitnessShiftStep{i}\n");}
    bridge+="namespace AspisR19.WitnessRootData\nopen RootCertificate ResidualModel SourceResidualPolynomial\nnoncomputable section\ndef roots : Fin 22 → M := fun i => (i.val+1:Nat)\ntheorem roots_list : List.ofFn roots=";
    bridge+=&format!("({:?}:List M) := by decide\n",(1..23).collect::<Vec<_>>());
    bridge+="theorem initial_vector : (fun j : Fin 27 => if j.val=0 then (1:M) else 0)=p0 := by\n  funext j\n  fin_cases j <;> decide\ntheorem root_chain : rootRun half (List.ofFn roots) p0=p22 := by\n  rw [roots_list]\n";
    for i in 0..22{bridge+=&format!("  apply root_step half {} _ p{i} p{} p22 (fun j => congrFun rootStep{:02} j)\n",i+1,i+1,i+1);}bridge+="  rfl\ntheorem root_coefficients (j : Fin 23) : rootCoefficients half roots j=p22 ⟨j.val,by omega⟩ := by\n  unfold rootCoefficients\n  rw [initial_vector,root_chain]\n";
    bridge+="theorem shift0 : shift half 0 p22=s0 := rfl\n";for i in 0..4{bridge+=&format!("theorem shift{} : shift half {} p22=s{} :=\n  shift_step half {i} p22 s{i} s{} shift{i} (fun r => congrFun shiftStep{} r)\n",i+1,i+1,i+1,i+1,i+1);}
    for n in["roots_list","initial_vector","root_chain","root_coefficients","shift0","shift1","shift2","shift3","shift4"]{bridge+=&format!("#print axioms {n}\n");}bridge+="end\nend AspisR19.WitnessRootData\n";files.insert("WitnessRootBridge.lean".into(),bridge);
    for(n,v)in &files{if checking{assert_eq!(std::fs::read_to_string(out.join(n)).unwrap(),*v,"generated drift: {n}");}else{std::fs::write(out.join(n),v).unwrap();}}
    println!("R38_ROOT_GENERATOR mode={} files={} root_steps=22 shift_steps=4 source_coordinate_checks={} zero_extension_checks=26 full_privacy=false",args[1],files.len(),source_checks);
}
