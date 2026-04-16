#![cfg(all(
    feature = "meta",
    feature = "runtime-tests",
    not(target_os = "windows")
))]

use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_apply_creates_subgoals() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut metam = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let goal = metam.mk_goal(&prop)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop.clone(), body, BinderInfo::Default)?;

        let state = match apply(&mut metam, TacticState::new(vec![goal]), &lambda) {
            TacticResult::Success(state) => state,
            TacticResult::Failure(e) => panic!("apply should create subgoals: {:?}", e),
        };

        assert_eq!(state.num_goals(), 1);
        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}
