from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs'];attrs='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
# The fixed-length arbitrary input constructor is only setup; the helper itself
# returns a borrow without traversing or copying the payload.
body='let v=kani::vec::exact_vec::<u8,58295>();let mut a=core::mem::ManuallyDrop::new(account());a.bytes=Ok(v);let original=a.bytes.as_ref().unwrap();let ptr=original.as_ptr();let len=original.len();let result=a.data();let exact=matches!(result,Ok(slice) if slice.as_ptr()==ptr&&slice.len()==len);assert!(exact);'
s+='\n'+attrs+'fn data_full_payload(){'+body+'}\n'+attrs+'fn data_full_payload_wrong(){'+body.replace('assert!(exact)','assert!(!exact)')+'}\n'
update({P+'NGL_owned.rs':s},'data_borrowed_payload')
