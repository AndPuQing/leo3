#![cfg(all(feature = "meta", feature = "runtime-tests"))]

use leo3::meta::*;
use leo3::prelude::*;

fn add_eq_axioms<'l>(
    lean: Lean<'l>,
    env: &LeanBound<'l, LeanEnvironment>,
) -> LeanResult<LeanBound<'l, LeanEnvironment>> {
    let u_name = LeanName::from_str(lean, "u")?;
    let u_level = LeanLevel::param(lean, u_name.clone())?;
    let level_params = LeanList::cons(u_name.cast(), LeanList::nil(lean)?)?;

    let alpha_name = LeanName::from_str(lean, "α")?;
    let lhs_name = LeanName::from_str(lean, "lhs")?;
    let rhs_name = LeanName::from_str(lean, "rhs")?;
    let a_name = LeanName::from_str(lean, "a")?;

    let sort_u = LeanExpr::sort(lean, u_level.clone())?;
    let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

    let alpha0 = LeanExpr::bvar(lean, 0)?;
    let alpha1 = LeanExpr::bvar(lean, 1)?;
    let alpha2 = LeanExpr::bvar(lean, 2)?;
    let eq_body = LeanExpr::forall(rhs_name, alpha0.clone(), prop, BinderInfo::Default)?;
    let eq_body = LeanExpr::forall(lhs_name, alpha1, eq_body, BinderInfo::Default)?;
    let eq_type =
        LeanExpr::forall(alpha_name.clone(), sort_u.clone(), eq_body, BinderInfo::Implicit)?;

    let eq_decl = LeanDeclaration::axiom(
        lean,
        LeanName::from_components(lean, "Eq")?,
        level_params.clone(),
        eq_type,
        false,
    )?;
    let env = LeanEnvironment::add_decl_unchecked(env, &eq_decl)?;

    let eq_const = LeanExpr::const_(
        lean,
        LeanName::from_components(lean, "Eq")?,
        LeanList::cons(u_level.cast(), LeanList::nil(lean)?)?,
    )?;
    let alpha_ref = LeanExpr::bvar(lean, 1)?;
    let a_ref1 = LeanExpr::bvar(lean, 0)?;
    let a_ref2 = LeanExpr::bvar(lean, 0)?;
    let eq_a_a = LeanExpr::mk_app(&eq_const, &[&alpha_ref, &a_ref1, &a_ref2])?;
    let refl_type = LeanExpr::forall(a_name, alpha2, eq_a_a, BinderInfo::Default)?;
    let refl_type = LeanExpr::forall(alpha_name, sort_u, refl_type, BinderInfo::Implicit)?;

    let refl_decl = LeanDeclaration::axiom(
        lean,
        LeanName::from_components(lean, "Eq.refl")?,
        level_params,
        refl_type,
        false,
    )?;
    LeanEnvironment::add_decl_unchecked(&env, &refl_decl)
}

#[test]
fn test_rfl_solves_equality() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let env = add_eq_axioms(lean, &env)?;
        let mut metam = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let levels = LeanList::cons(LeanLevel::zero(lean)?.cast(), LeanList::nil(lean)?)?;
        let eq_goal = LeanExpr::mk_eq(lean, levels, &prop, &prop, &prop)?;
        let goal = metam.mk_goal(&eq_goal)?;

        let state = match rfl(&mut metam, TacticState::new(vec![goal])) {
            TacticResult::Success(state) => state,
            TacticResult::Failure(e) => panic!("rfl should solve a reflexive equality: {:?}", e),
        };

        assert!(state.is_solved());
        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}
