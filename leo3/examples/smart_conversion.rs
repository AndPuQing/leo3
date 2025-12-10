//! Example demonstrating conversion macros

use leo3::prelude::*;

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Vec<u8> uses optimized memcpy
        let data = vec![1u8, 2, 3, 4, 5];
        let ba = to_lean!(data.clone(), lean, Vec<u8>)?;
        let recovered: Vec<u8> = from_lean!(&ba, Vec<u8>)?;
        assert_eq!(recovered, data);

        // Byte slice
        let slice = b"Hello";
        let ba = to_lean!(slice, lean, &[u8])?;
        assert_eq!(LeanByteArray::size(&ba), 5);

        // Generic Vec<T>
        let numbers = vec![10u64, 20, 30];
        let arr = to_lean!(numbers.clone(), lean)?;
        let recovered: Vec<u64> = from_lean!(&arr, Vec<u64>)?;
        assert_eq!(recovered, numbers);

        println!("All conversions successful");
        Ok(())
    })
}
