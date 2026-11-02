// Independent safe borrowed reference for the frozen getter, generic raw values.
pub fn selected<T>(start:usize,index:usize,rows:&[[T;5]])->&[T;5] {&rows[index-start]}
