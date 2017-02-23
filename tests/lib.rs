extern crate dfc;

use dfc::{DFC_New, DFC_AddPattern, DFC_Compile, DFC_Search, DFC_FreeStructure};
use std::ffi::CStr;

#[test]
fn success_dfc() {
    unsafe {
        // Init a dfc structure
        let dfc = DFC_New();
        assert!(!dfc.is_null());

        let buf = b"This input includes an attack pattern. It might CRASH your machine.\0";
        let pat1 = b"attack\0";
        let pat2 = b"crash\0";
        let pat3 = b"Piolink\0";
        let pat4 = b"ATTACK\0";

        // Add some pattersn
        DFC_AddPattern(dfc, pat1.as_ptr(), pat1.len() - 1, false, 0);
        DFC_AddPattern(dfc, pat2.as_ptr(), pat2.len() - 1, true, 1);
        DFC_AddPattern(dfc, pat3.as_ptr(), pat3.len() - 1, true, 2);
        DFC_AddPattern(dfc, pat4.as_ptr(), pat4.len() - 1, true, 3);

        // Compile the structure
        // TODO: crashes in lib.rs:433
        // DFC_Compile(dfc);

        // Search
        DFC_Search(dfc, buf.as_ptr(), buf.len(), print_result);

        // Cleanup;
        DFC_FreeStructure(dfc);
    }
}

fn print_result(pattern: *const u8, id_list: *const u32, list_size: usize) {
    unsafe {
        println!("Found match in pattern: '{}'",
                 CStr::from_ptr(pattern as *const i8).to_str().unwrap());
        for i in 0..list_size {
            println!("{}", *id_list.offset(i as isize));
        }
    }
}
