#![cfg(all(
    feature = "meta",
    feature = "runtime-tests",
    not(target_os = "windows")
))]

use leo3::meta::*;
use leo3::prelude::*;

fn build_prop_identity_type<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanExpr>> {
    let p_name = LeanName::from_str(lean, "P")?;
    let h_name = LeanName::from_str(lean, "h")?;
    let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
    let bvar0 = LeanExpr::bvar(lean, 0)?;
    let bvar1 = LeanExpr::bvar(lean, 1)?;
    let inner = LeanExpr::forall(h_name, bvar0, bvar1, BinderInfo::Default)?;
    LeanExpr::forall(p_name, prop, inner, BinderInfo::Default)
}

#[test]
fn test_tactic_intro_then_exact() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut metam = MetaMContext::new(lean, env)?;

        let target_type = build_prop_identity_type(lean)?;
        let goal = metam.mk_goal(&target_type)?;
        let state = TacticState::new(vec![goal]);

        let p_name = LeanName::from_str(lean, "P")?;
        let state = match intro(&mut metam, state, &p_name) {
            TacticResult::Success(state) => state,
            TacticResult::Failure(e) => panic!("intro should succeed: {:?}", e),
        };

        assert_eq!(state.num_goals(), 1);
        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}
