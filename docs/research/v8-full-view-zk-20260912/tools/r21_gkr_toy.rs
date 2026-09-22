//! Plumbing preflight only, NOT ordinary-terminal source evidence.
mod r21_gkr;
use r21_gkr::{Circuit,Gate,Input,integer,prove,verify};
fn main(){
    static I:[Input;4]=[Input::Public(0),Input::Public(1),Input::Public(2),Input::Constant([0,0,0,0])];
    static A:[Gate;4]=[Gate(1,0,1),Gate(2,1,2),Gate(0,0,2),Gate(3,2,3)];
    static B:[Gate;2]=[Gate(1,0,1),Gate(0,2,3)];
    static C:[Gate;1]=[Gate(2,0,1)];
    static L:[&[Gate];3]=[&A,&B,&C];
    let circuit=Circuit{id:[21;32],inputs:&I,layers:&L};let context=[9;32];
    let mut checks=0;
    for case in 0..12u32{
        let inputs=core::array::from_fn(|j|integer(case+3*j as u32));
        let (out,proof)=prove(&circuit,&context,&inputs).unwrap();
        let a=inputs[0];let b=inputs[1];let c=inputs[2];
        assert_eq!(out,a.mul(b).mul(b.sub(c)).sub(a.add(c).add(c)));
        assert!(verify(&circuit,&context,&inputs,out,&proof).is_ok());
        assert!(verify(&circuit,&context,&inputs,out.add(integer(1)),&proof).is_err());checks+=2;
        for i in 0..proof.len()/16{let mut bad=proof.clone();bad[16*i]^=1;assert!(verify(&circuit,&context,&inputs,out,&bad).is_err());checks+=1;}
        let mut changed=inputs;changed[0]=changed[0].add(integer(1));
        assert!(verify(&circuit,&context,&changed,out,&proof).is_err());
        assert!(verify(&circuit,&[8;32],&inputs,out,&proof).is_err());
        assert!(verify(&circuit,&context,&inputs,out,&proof[..proof.len()-1]).is_err());checks+=3;
    }
    println!("R21_GKR_TOY cases=12 checks={checks} source_terminal=false security_theorem=false");
}
