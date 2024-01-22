import Snlean.Lambda

namespace Soundness

open Lambda
open Lambda.Reduction

-- open Lambda.value

-- theorem env_var_rule_noemp : ∀ (x : String) (T : Ty) (Γ : TyCtx),
--   (Γ ⊢ ` x : T) →
--   Γ ≠ nil
-- := by
--   intro x T Γ ht env_is_emp;
--   cases ht with
--   | tyVar env_isnt_emp =>
--     rw [env_is_emp] at env_isnt_emp
--     contradiction

theorem progress :
  ∅ ⊢ t : T → Value t ∨ (∃t' : Term, t —→ t')
:= by
  intro jt;
  cases jt with
  -- Contradictory because env_is_emp contradicts x_elem_env
  | tyVar _ => contradiction
  -- Straightforward because t is value
  | tyAbs _ => exact Or.inl Value.lam
  | tyApp jt1 jt2 =>
    cases progress jt1 with
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
          cases progress jt2 with
          -- (λ x1 : T1. t1) $ v —→ [x1 := v] t1
          | inl t2_is_value =>
            cases t2_is_value with
            | lam =>
              apply Exists.intro
              apply eAppAbs
          | inr t2_canbe_reduced =>
            cases t2_canbe_reduced with
            | intro _ t2_canbe_reduced' =>
              apply Exists.intro
              apply eAppRight
              apply Value.lam
              apply t2_canbe_reduced'

theorem subst_preservation :
  Γ ⊢ s : S →
  (x, S) :: Γ ⊢ t : T →
  Γ ⊢ [x := s] t : T
:= by
  sorry

theorem preservation :
  Γ ⊢ e : T ∧ Reduction e e' →
  Γ ⊢ e' : T
:= by
  sorry
  -- intro e e' T Γ assum;
  -- have wte := And.left assum;
  -- have ev := And.right assum;
  -- induction ev with
  -- | eAppAbs T e1body v2 v2_is_value =>
  --   sorry
  -- | eAppLeft e1 e1' e2 eve1 ihe1 =>
  --   cases wte with
  --   | tyApp Γ e1 e2 T1 T2 je1 wte2 =>
  --     apply ihe1 (And.intro je1 eve1)
  -- | eAppRight v1 e2 e2' v1_is_value eve2 ihe2 =>
  --   sorry




  -- induction wte with
  -- | tyVar _ _ _ pre =>
  --   -- Contradictory to ev bacause var cannot be evaluated
  --   contradiction
  -- | tyAbs =>
  --   -- Contradictory to ev bacause lam is a value and no rules evaluate it
  --   contradiction
  -- | tyApp Γ e1 e2 T1 T2 je1 wte2 ihe1 ihe2 =>
  --   cases ev with
  --   -- eAppAbs : ∀ (t : Ty) (e v : Term), value v → (app (lam t e) v) —→ (subst e 0 v)
  --   | eAppAbs T e v v_is_value =>
  --     sorry
  --   -- eAppLeft : ∀ (e1 e1' e2 : Term), e1 —→ e1' → (app e1 e2) —→ (app e1' e2)
  --   | eAppLeft e1 e1' e2 eve1 =>
  --     sorry
  --   -- eAppRight : ∀ (v e2 e2' : Term), value v → e2 —→ e2' → (app v e2) —→ (app v e2')
  --   | eAppRight v e2 e2' v_is_value eve2 =>
  --     sorry
