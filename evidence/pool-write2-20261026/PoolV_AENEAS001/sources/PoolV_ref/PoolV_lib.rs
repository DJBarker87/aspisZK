//! P6 reference for the PURE chronology tail; native coupling is separate.
pub fn chronology_scan(new: [u64;8], old: [u64;8]) -> (bool,bool) {
    let mut i=0;let mut decreased=false;let mut progressed=false;
    while i<8 {
        decreased |= new[i]<old[i];
        progressed |= new[i]>old[i];
        i+=1;
    }
    (decreased,progressed)
}
pub fn chronology(new:[u64;8],old:[u64;8],has:bool,sequence:u64)->(u8,u64){
    let (decreased,progressed)=chronology_scan(new,old);
    if has && decreased {(1,0)} else if has && !progressed {(2,0)}
    else if sequence==u64::MAX {(3,0)} else {(0,sequence+1)}
}
