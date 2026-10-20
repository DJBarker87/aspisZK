pub fn all<'a,T,F>(iter:&mut core::slice::Iter<'a,T>,mut f:F)->bool where F:FnMut(&'a T)->bool {
                while let Some(x) = iter.next() {
                    if !f(x) {
                        return false;
                    }
                }
                true
            }
pub fn ok_or<T,E>(value:Option<T>,err:E)->Result<T,E> {
        match value {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }
