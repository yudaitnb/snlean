import Snlean.Lambda

namespace Soundness

open Lambda
open Lambda.Reduction

-- Issues
-- progressの停止性
-- preservationのihe1, ihe2の形式

theorem progress :
  ∅ ⊢ t : T → Value t ∨ (∃t' : Term, t —→ t')
:= by
  intro jt;
  cases jt with
  -- Contradictory because env_is_emp contradicts x_elem_env
  | tyVar _ => contradiction
  -- Straightforward because t is value
  | tyAbs _ => exact Or.inl Value.lam
  | @tyApp _ _ _ _ e2 jt1 jt2 =>
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
        | @lam x _ e =>
          cases progress jt2 with
          -- (λ x1 : T1. t1) $ v —→ [x1 := v] t1
          | inl t2_is_value =>
              -- apply (Exists.intro _ (eAppAbs t2_is_value))
              apply Exists.intro
              apply eAppAbs
              apply (subst e x e2) -- なんでもOK
              apply t2_is_value
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
  Γ ⊢ e : T →
  e —→ e' →
  Γ ⊢ e' : T
:= by
  intro je eve;
  induction je with
  | tyVar =>
    -- Contradictory to ev bacause var cannot be evaluated
    contradiction
  | tyAbs =>
    -- Contradictory to ev bacause lam is a value and no rules evaluate it
    contradiction
  | tyApp je1 je2 ihe1 ihe2 =>
    cases eve with
    -- eAppAbs : ∀ (t : Ty) (e v : Term), value v → (app (lam t e) v) —→ (subst e 0 v)
    | eAppAbs v_is_value =>
      sorry
    -- eAppLeft : ∀ (e1 e1' e2 : Term), e1 —→ e1' → (app e1 e2) —→ (app e1' e2)
    | eAppLeft eve1 =>
      sorry
    -- eAppRight : ∀ (v e2 e2' : Term), value v → e2 —→ e2' → (app v e2) —→ (app v e2')
    | eAppRight v_is_value eve2 =>
      sorry
