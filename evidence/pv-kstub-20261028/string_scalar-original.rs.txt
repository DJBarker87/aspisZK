fn string_scalar() {
        let scalar:u32=kani::any();
        if let Some(c)=char::from_u32(scalar) {
            let owned=c.to_string(); let path:&std::path::Path=owned.as_ref();
            assert_eq!(path.as_os_str().as_bytes(),reference::borrow_bytes(owned.as_bytes()));
        }
    }