pub fn qeq_ref(a:[u32;4],b:[u32;4])->bool{a[0]==b[0]&&a[1]==b[1]&&a[2]==b[2]&&a[3]==b[3]}
pub fn roweq_ref(a:[[u32;4];4],b:[[u32;4];4])->bool{qeq_ref(a[0],b[0])&&qeq_ref(a[1],b[1])&&qeq_ref(a[2],b[2])&&qeq_ref(a[3],b[3])}
pub fn guard_raw_ref(variant:u8,folds:usize,a:[[u32;4];4],b:[[u32;4];4],c:[[u32;4];4],d:[[u32;4];4])->bool{variant==1&&folds==2&&roweq_ref(a,b)&&roweq_ref(c,d)}
