fn wide_flat() {
        let raw:[u32;8]=kani::any();
        let x=aspis_core::field::WideExact::new(q([raw[0],raw[1],raw[2],raw[3]]),q([raw[4],raw[5],raw[6],raw[7]]));
        assert_eq!(x.to_le_bytes(),super::reference_p6::wide_bytes_flat(x));
    }