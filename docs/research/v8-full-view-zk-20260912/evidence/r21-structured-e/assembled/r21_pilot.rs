//! Public-only honest prover and source differential. No witness arguments.
mod r21_gkr;
mod r21_circuit;
mod r21_native;
use aspis_core::field::{QM31 as K,CM31,M31,P};
use r21_circuit::CIRCUIT;
fn sample(s:&mut u64)->K{
    let mut next=||{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;M31((*s as u32)%P)};
    K{c0:CM31::new(next(),next()),c1:CM31::new(next(),next())}
}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert!(args.len()==2||args.len()==4,"output-dir [public-inputs.bin context.bin]");
    let out=std::path::Path::new(&args[1]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    r21_gkr::r21_wiring::check(&CIRCUIT);
    let mut seed=0x7262_2100_cafe_beefu64;
    for case in 0..160{
        let input:[K;24]=core::array::from_fn(|_|if case==0{K::ZERO}else if case==1{K::ONE}else if case==2{K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))}}else{sample(&mut seed)});
        let native=r21_native::compute(&input);let graph=r21_gkr::evaluate(&CIRCUIT,&input);
        assert_eq!(native,graph.last().unwrap()[0],"source differential {case}");
    }
    println!("R21_SOURCE_DIFF cases=160 full_QM31=true arbitrary_finals=true max_limbs=true");
    let input:[K;24]=if args.len()==4{let b=std::fs::read(&args[2]).unwrap();assert_eq!(b.len(),384);core::array::from_fn(|i|K::from_le_bytes(&b[16*i..16*i+16]).unwrap())}else{core::array::from_fn(|_|sample(&mut seed))};
    let context:[u8;32]=if args.len()==4{std::fs::read(&args[3]).unwrap().try_into().unwrap()}else{[21;32]};
    let (output,proof)=r21_gkr::prove(&CIRCUIT,&context,&input).unwrap();
    assert_eq!(output,r21_native::compute(&input));
    assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output,&proof).is_ok());
    assert!(r21_gkr::verify_reference(&CIRCUIT,&context,&input,output,&proof).is_ok());
    // Every coefficient/endpoint in every layer, not just one example message.
    for i in 0..proof.len()/16{
        let mut bad=proof.clone();let x=K::from_le_bytes(&bad[16*i..16*i+16]).unwrap().add(K::ONE);
        x.write_le_bytes(&mut bad[16*i..16*i+16]);
        assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output,&bad).is_err(),"message {i}");
    }
    for i in 0..24{let mut bad=input;bad[i]=bad[i].add(K::ONE);assert!(r21_gkr::verify(&CIRCUIT,&context,&bad,output,&proof).is_err(),"input binding {i}");}
    assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output.add(K::ONE),&proof).is_err());
    let mut bad_context=context;bad_context[0]^=1;assert!(r21_gkr::verify(&CIRCUIT,&bad_context,&input,output,&proof).is_err());
    let changed=CIRCUIT.id.map(|x|x^1);let wrong=r21_gkr::Circuit{id:changed,inputs:CIRCUIT.inputs,layers:CIRCUIT.layers};
    assert!(r21_gkr::verify(&wrong,&context,&input,output,&proof).is_err());
    assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output,&proof[..proof.len()-1]).is_err());
    let mut extra=proof.clone();extra.push(0);assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output,&extra).is_err());
    // Fixed header: 24 canonical public fields, one claimed output, context32.
    let mut wire=vec![0u8;432];for(i,&v)in input.iter().enumerate(){v.write_le_bytes(&mut wire[16*i..16*i+16]);}
    output.write_le_bytes(&mut wire[384..400]);wire[400..432].copy_from_slice(&context);wire.extend_from_slice(&proof);
    std::fs::write(out.join("helper.bin"),&wire).unwrap();
    println!("R21_PILOT accepted=true source_inputs={} proof_bytes={} tampered_message_fields={} input_bindings=24 wrong_output=true wrong_context=true wrong_circuit=true framing=true security_theorem=false",args.len()==4,proof.len(),proof.len()/16);
}
