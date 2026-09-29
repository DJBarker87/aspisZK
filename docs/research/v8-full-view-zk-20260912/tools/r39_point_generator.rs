//! Staged literal certificates for the existing R37 algebraic witness.
include!("r37_residual_arithmetic.rs");
fn residues(p:&[K])->Vec<u32>{p.iter().map(|v|{let mut b=[0;16];v.write_le_bytes(&mut b);assert_eq!(&b[4..],&[0;12]);u32::from_le_bytes(b[..4].try_into().unwrap())}).collect()}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);assert!(args[1]=="--write"||args[1]=="--check");let out=std::path::Path::new(&args[2]);let checking=args[1]=="--check";
    if !checking{assert!(!out.exists());std::fs::create_dir(out).unwrap();}
    let z:[K;10]=std::array::from_fn(|i|K::ONE.mul_m31(M31(i as u32+2)));
    let abc=[K::ONE.mul_m31(M31(7)),K::ONE.mul_m31(M31(5)),K::ONE.mul_m31(M31(5)).neg()];
    let map=basis_transport::transport();assert_eq!(map.order.as_slice(),&fixed::ORDER);assert_eq!(map.inactive.as_slice(),&fixed::INACTIVE);
    let source_points=corelib::v6_transcript::v6_statement_points(&z);
    let mut coords=Vec::new();let mut codes=Vec::new();let mut weights=Vec::new();let mut pivot_negative=0;
    for which in 0..3{
        let p=point(&z,which);assert_eq!(p,source_points[which]);
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,p.to_vec()).unwrap();
        let dense:Vec<_>=(0..1024).map(|i|w.weight_at(i)).collect();for r in 0..1024{assert_eq!(tensor(&p,r),dense[r]);}
        let code:[K;111]=std::array::from_fn(|j|tensor(&p,fixed::ORDER[j]).sub(if fixed::INACTIVE[fixed::ORDER[j]]{tensor(&p,1023)}else{K::ZERO}));
        let source_code=map.dual(&dense);assert_eq!(code.as_slice(),&source_code[..111]);
        let source_weight=opening_weights::chord_transpose(&source_code,abc);
        let weight:[K;108]=std::array::from_fn(|r|(0..111).fold(K::ZERO,|s,j|s.add(code[j].mul(centry(r,j,abc)))));
        assert_eq!(weight.as_slice(),&source_weight[..108]);
        for r in 0..108{let bad=(0..111).fold(K::ZERO,|s,j|s.add(tensor(&p,fixed::ORDER[j]).mul(centry(r,j,abc))));if bad!=weight[r]{pivot_negative+=1;}}
        coords.push(p);codes.push(code);weights.push(weight);
    }
    assert!(pivot_negative>0);
    let mut files=std::collections::BTreeMap::<String,String>::new();
    let header="/- Generated staged point-weight certificate. Do not inline earlier stages. -/\n";
    let ns="namespace AspisR19.WitnessPointData\nopen RootCertificate ResidualModel\nnoncomputable section\n";
    let end="end\nend AspisR19.WitnessPointData\n";
    let support:Vec<String>=(0..108).map(|r|format!("({{{}}}:Finset (Fin 111))",(0..111).filter(|&j|centry(r,j,abc)!=K::ZERO).map(|j|j.to_string()).collect::<Vec<_>>().join(","))).collect();
    let mut data=format!("{header}import AspisV8R19.PointWeightCertificate\nimport Mathlib.Tactic.FinCases\n{ns}def z : Fin 10 → M := PointWeightCertificate.vector {:?}\n",residues(&z));
    for i in 0..3{data+=&format!("def coords{i} : Fin 10 → M := PointWeightCertificate.vector {:?}\ndef code{i} : Fin 111 → M := PointWeightCertificate.vector {:?}\ndef weights{i} : Fin 108 → M := PointWeightCertificate.vector {:?}\n",residues(&coords[i]),residues(&codes[i]),residues(&weights[i]));}
    data+=end;files.insert("WitnessPointData.lean".into(),data);
    for chunk in 0..9{let mut body=format!("{header}import AspisV8R19.WitnessPointData\n{ns}");for r in chunk*12..(chunk+1)*12{body+=&format!("theorem chord_support{r} : ∀ j : Fin 111, j ∉ {} → chordEntry half (7:M) 5 (-5) {r} j.val = 0 := by\n  intro j\n  fin_cases j <;> decide\n#print axioms chord_support{r}\n",support[r]);}body+=end;files.insert(format!("WitnessChordSupport{chunk:02}.lean"),body);}
    let mut points=format!("{header}import AspisV8R19.WitnessPointData\n{ns}");
    for i in 0..3{points+=&format!("theorem point{i} : point z {i} = coords{i} := by\n  funext j\n  fin_cases j <;> decide\n#print axioms point{i}\n");}points+=end;files.insert("WitnessPoints.lean".into(),points);
    let mut bridge=String::from(header);bridge+="import AspisV8R19.WitnessPoints\n";
    for i in 0..3{for (kind,n) in [("Code",111),("Weight",108)]{for chunk in 0..(n+11)/12{
        let name=format!("Witness{kind}{i}Chunk{chunk:02}");bridge+=&format!("import AspisV8R19.{name}\n");
        let imports=if kind=="Weight"{format!("import AspisV8R19.WitnessChordSupport{chunk:02}\n")}else{String::new()};
        let mut body=format!("{header}import AspisV8R19.WitnessPointData\n{imports}{ns}");
        for j in chunk*12..std::cmp::min((chunk+1)*12,n){let theorem=format!("{}{i}_{j}",kind.to_lowercase());let expr=if kind=="Code"{format!("codeWeight ResidualPins.order ResidualPins.inactive coords{i} ({j}:Fin 111) = code{i} {j}")}else{format!("(∑ j : Fin 111, code{i} j * chordEntry half (7:M) 5 (-5) {j} j.val) = weights{i} {j}")};
            let proof=if kind=="Weight"{format!("by\n  rw [PointWeightCertificate.sparse_sum _ _ _ chord_support{j}]\n  decide")}else{"by decide".into()};
            body+=&format!("theorem {theorem} : {expr} := {proof}\n#print axioms {theorem}\n");
        }body+=end;files.insert(name+".lean",body);
    }}}
    bridge+=ns;
    for i in 0..3{
        bridge+=&format!("theorem code_stage{i} : codeWeight ResidualPins.order ResidualPins.inactive coords{i} = code{i} := by\n  funext j\n  fin_cases j\n");for j in 0..111{bridge+=&format!("  · exact code{i}_{j}\n");}
        bridge+=&format!("theorem weight_stage{i} (r : Fin 108) : (∑ j : Fin 111, code{i} j * chordEntry half (7:M) 5 (-5) r.val j.val) = weights{i} r := by\n  fin_cases r\n");for j in 0..108{bridge+=&format!("  · exact weight{i}_{j}\n");}
        bridge+=&format!("theorem point_weight{i} (r : Fin 108) : pointWeight ResidualPins.order ResidualPins.inactive half (7:M) 5 (-5) z {i} r.val = weights{i} r :=\n  PointWeightCertificate.point_weight_stages _ _ _ _ _ _ _ _ _ _ _ point{i} code_stage{i} weight_stage{i} r\n#print axioms code_stage{i}\n#print axioms weight_stage{i}\n#print axioms point_weight{i}\n");
    }bridge+=end;files.insert("WitnessPointBridge.lean".into(),bridge);
    // One expensive-shaped cell is a separate preflight, before full chunks.
    files.insert("WitnessPointPreflight.lean".into(),format!("{header}import AspisV8R19.WitnessPointData\n{ns}theorem code_preflight : codeWeight ResidualPins.order ResidualPins.inactive coords1 (107:Fin 111) = code1 107 := by decide\ntheorem sparse_preflight : ∀ j : Fin 111, j ∉ {} → chordEntry half (7:M) 5 (-5) 107 j.val = 0 := by\n  intro j\n  fin_cases j <;> decide\ntheorem weight_preflight : (∑ j : Fin 111, code1 j * chordEntry half (7:M) 5 (-5) 107 j.val) = weights1 107 := by\n  rw [PointWeightCertificate.sparse_sum _ _ _ sparse_preflight]\n  decide\n#print axioms code_preflight\n#print axioms sparse_preflight\n#print axioms weight_preflight\n{end}",support[107]));
    for(n,v)in &files{if checking{assert_eq!(std::fs::read_to_string(out.join(n)).unwrap(),*v,"generated drift: {n}");}else{std::fs::write(out.join(n),v).unwrap();}}
    println!("R39_POINT_GENERATOR mode={} files={} table_checks=2048 point_checks=30 tensor_checks=3072 code_checks=333 weight_checks=324 pivot_negative_entries={} full_privacy=false",args[1],files.len(),pivot_negative);
}
