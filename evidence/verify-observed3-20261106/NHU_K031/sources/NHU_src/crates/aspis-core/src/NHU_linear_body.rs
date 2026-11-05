fn NHU_linear_step(point:&[QM31;10],mut suffix:QM31,mut weighted:QM31,n:usize)->(QM31,QM31,usize){
let mut iter=(0..n).rev();
if let Some(variable)=iter.next(){
        suffix = suffix.add(point[variable]);
        if variable != 0 {
            weighted = weighted.add(suffix);
        }
    
}
(suffix,weighted,iter.len())
}
