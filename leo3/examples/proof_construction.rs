//! Example: Proof Construction with Leo3
//!
//! Demonstrates building proof terms, validating them with MetaM,
//! and adding them to a Lean environment as theorems.

use leo3::meta::*;
use leo3::prelude::*;

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        println!("=== Proof Construction Example ===\n");

        let env = LeanEnvironment::empty(lean, 0)?;

        // ----------------------------------------------------------------
        // 1. Build a theorem: ∀ (P : Prop), P → P
        //    Proof: λ (P : Prop) (h : P), h
        // ----------------------------------------------------------------
        println!("1. Building theorem: forall (P : Prop), P -> P");

        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Type: forall (P : Sort 0), forall (h : bvar 0), bvar 1
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let thm_type = LeanExpr::forall(p_name.clone(), prop, inner_forall, BinderInfo::Default)?;

        // Value: lambda (P : Sort 0), lambda (h : bvar 0), bvar 0
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0a = LeanExpr::bvar(lean, 0)?;
        let bvar0b = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0a, bvar0b, BinderInfo::Default)?;
        let proof = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

        println!("   Type kind:  {:?}", LeanExpr::kind(&thm_type));
        println!("   Proof kind: {:?}", LeanExpr::kind(&proof));

        // ----------------------------------------------------------------
        // 2. Validate the proof using MetaM
        // ----------------------------------------------------------------
        println!("\n2. Validating proof with MetaM...");

        let mut ctx = MetaMContext::new(lean, env.clone())?;

        // Type-check the proof
        ctx.check(&proof)?;
        println!("   Proof is well-typed");

        // Infer the type of the proof
        let inferred = ctx.get_proof_type(&proof)?;
        println!("   Inferred type kind: {:?}", LeanExpr::kind(&inferred));

        // Verify the proof proves the proposition
        assert!(ctx.is_proof_of(&proof, &thm_type)?);
        println!("   Proof proves the proposition");

        // Verify the proposition is indeed a Prop
        assert!(ctx.is_prop(&thm_type)?);
        println!("   Proposition lives in Prop");

        // ----------------------------------------------------------------
        // 3. Add the theorem to the environment
        // ----------------------------------------------------------------
        println!("\n3. Adding theorem to environment...");

        let thm_name = LeanName::from_str(lean, "id_prop")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, level_params, thm_type, proof)?;
        let env = LeanEnvironment::add_decl(&env, &decl)?;
        println!("   Theorem 'id_prop' added (kernel type-checked)");

        // ----------------------------------------------------------------
        // 4. Retrieve and inspect the theorem
        // ----------------------------------------------------------------
        println!("\n4. Inspecting theorem from environment...");

        let lookup = LeanName::from_str(lean, "id_prop")?;
        let cinfo = LeanEnvironment::find(&env, &lookup)?.expect("theorem should exist");

        println!("   Kind:      {}", LeanConstantInfo::kind(&cinfo));
        println!("   Has value: {}", LeanConstantInfo::has_value(&cinfo));

        let found_type = LeanConstantInfo::type_(&cinfo)?;
        println!("   Type kind: {:?}", LeanExpr::kind(&found_type));

        if let Some(value) = LeanConstantInfo::value(&cinfo)? {
            println!("   Value kind: {:?}", LeanExpr::kind(&value));
        }

        println!("\n=== All proof operations completed successfully! ===");
        Ok(())
    })
}
