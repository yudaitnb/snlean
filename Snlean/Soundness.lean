import Snlean.Lambda

open Lambda

namespace Soundness

open TyCtx TyCtx.HasType
open Term Term.Reduction

-- Issues
-- progressの停止性
-- preservationのihe1, ihe2の形式

theorem progress :
  Γ ⊢ t : T ∧ (Γ = nil) → Value t ∨ (∃t' : Term, t —→ t')
:= by
  intro assum;
  have jt := And.left assum;
  have env_is_emp := And.right assum;
  induction jt with
  -- Contradictory because env_is_emp contradicts x_elem_env
  | tyVar x_elem_env =>
    rw [env_is_emp] at x_elem_env
    contradiction
  -- Straightforward because t is value
  | tyAbs _ => exact Or.inl Value.lam
  | tyApp jt1 jt2 ihe1 ihe2 =>
    have pre_ihe1 := And.intro jt1 env_is_emp;
    cases ihe1 pre_ihe1 env_is_emp with
    | inr t1_canbe_reduced =>
      cases t1_canbe_reduced with
      | intro t1' t1_canbe_reduced' =>
        apply Or.intro_right
        apply Exists.intro
        apply eAppLeft
        exact t1_canbe_reduced'
    | inl t1_is_value =>
      apply Or.intro_right
      cases t1_is_value with
        | lam =>
          have pre_ihe2 := And.intro jt2 env_is_emp;
          cases ihe2 pre_ihe2 env_is_emp with
          -- (λ x1 : T1. t1) $ v —→ [x1 := v] t1
          | inl t2_is_value =>
            cases t2_is_value with
            | lam =>
              apply Exists.intro
              apply eAppAbs
              apply Value.lam
          | inr t2_canbe_reduced =>
            cases t2_canbe_reduced with
            | intro _ t2_canbe_reduced' =>
              apply Exists.intro
              apply eAppRight
              apply Value.lam
              apply t2_canbe_reduced'


theorem subst_preservation :
  Γ ⊢ s : S →
  Γ' ⊢ t : T ∧ (Γ' = (Γ ‚ x : S)) →
  Γ ⊢ [x := s] t : T
:= by
  intro js assum_t;
  have jt := And.left assum_t;
  have x_elem_gamma' := And.right assum_t;
  sorry
--   induction jt with
--   | tyVar y_elem_env =>
--     sorry
--     -- cases y_elem_env with
--     -- | intro y_ty y_elem_env' =>
--     --   cases y_elem_env' with
--     --   | Or.inl y_is_x =>
--     --     rw [←y_is_x]
--     --     apply js
--     --   | Or.inr y_elem_env'' =>
--     --     apply tyVar
--     --     apply y_elem_env''
--   | tyAbs jt' =>

--     apply tyAbs
--     apply jt'
--   | tyApp jt1 jt2 ihe1 ihe2 =>
--     apply tyApp
--     apply ihe1
--     apply ihe2

theorem preservation :
  Γ ⊢ e : T →
  e —→ e' →
  Γ ⊢ e' : T
:= by
  intro je;
  revert e';
  induction je with
  | tyVar =>
    -- Contradictory to ev bacause var cannot be evaluated
    intros
    contradiction
  | tyAbs =>
    -- Contradictory to ev bacause lam is a value and no rules evaluate it
    intros
    contradiction
  | tyApp je1 je2 ihe1 ihe2 =>
    intros e' eve
    cases eve with
    -- eAppAbs : ∀ (t : Ty) (e v : Term), value v → (app (lam t e) v) —→ (subst e 0 v)
    | eAppAbs v_is_value =>
      apply subst_preservation
      apply je2
      apply And.intro
      cases je1 with
      | tyAbs jt =>
        apply jt
        trivial
    -- eAppLeft : ∀ (e1 e1' e2 : Term), e1 —→ e1' → (app e1 e2) —→ (app e1' e2)
    | eAppLeft eve1 =>
      apply tyApp
      apply ihe1
      apply eve1
      apply je2
    -- eAppRight : ∀ (v e2 e2' : Term), value v → e2 —→ e2' → (app v e2) —→ (app v e2')
    | eAppRight v_is_value eve2 =>
      apply tyApp
      apply je1
      apply ihe2
      apply eve2
