//! Test literal type
use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_literal_type_minimal() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Test constant expression creation
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let empty_levels = leo3::types::LeanList::nil(lean)?;
        let nat_const = LeanExpr::const_(lean, nat_name, empty_levels)?;
        assert!(LeanExpr::is_const(&nat_const));

        // Test literal type for Nat
        let nat_lit = LeanLiteral::nat(lean, 42)?;
        let lit_type = LeanLiteral::type_(&nat_lit)?;
        assert!(LeanExpr::is_const(&lit_type));

        // Test literal type for String
        let str_lit = LeanLiteral::string(lean, "hello")?;
        let str_type = LeanLiteral::type_(&str_lit)?;
        assert!(LeanExpr::is_const(&str_type));

        // Nat and String types should be different
        assert!(!LeanExpr::equal(&lit_type, &str_type));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}
