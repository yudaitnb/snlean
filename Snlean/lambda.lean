import Std.Data.List.Init.Lemmas
import Std.Data.List.Lemmas

inductive type
| base : type
| arrow : type → type → type
deriving BEq

open type

inductive term
| var : Nat → term
| abs : type → term → term
| app : term → term → term
deriving BEq

open term

def type_env := List (Nat × type)
  deriving BEq

inductive has_type : type_env → term → type → Prop
| var_rule : ∀ (gamma : type_env) (x : Nat) (t : type), gamma.elem (x, t) → has_type gamma (var x) t
| abs_rule : ∀ (gamma : type_env) (x : Nat) (t1 t2 : type) (e : term), has_type ((x, t1) :: gamma) e t2 → has_type gamma (abs t1 e) (type.arrow t1 t2)
| app_rule : ∀ (gamma : type_env) (e1 e2 : term) (t2 t1 : type), has_type gamma e1 (type.arrow t2 t1) → has_type gamma e2 t2 → has_type gamma (app e1 e2) t1
open has_type

inductive value : term → Prop
| abs : ∀ (t : type) (e : term), value (abs t e)

def subst (t : term) (idx : Nat) (s : term) : term :=
  match t with
  | var x     => if x = idx then s else (var x)
  | abs t e   => abs t (subst e (idx + 1) s)
  | app e1 e2 => app (subst e1 idx s) (subst e2 idx s)

inductive eval : term → term → Prop
| e_app_abs : ∀ (t : type) (e v : term), value v → eval (app (abs t e) v) (subst e 0 v)
| e_app_left : ∀ (e1 e1' e2 : term), eval e1 e1' → eval (app e1 e2) (app e1' e2)
| e_app_right : ∀ (v e2 e2' : term), value v → eval e2 e2' → eval (app v e2) (app v e2')
open eval

theorem env_var_rule_noemp : ∀ (x : Nat) (T : type) (gamma : type_env), has_type gamma (var x) T → gamma ≠ [] := by
  intro x T gamma ht env_is_emp;
  cases ht with
  | var_rule _ _ _ env_is_not_emp =>
    rw [env_is_emp] at env_is_not_emp
    contradiction

theorem progress : ∀ (t : term) (T : type) (gamma : type_env), has_type gamma t T ∧ gamma = [] → value t ∨ (∃t' : term, eval t t') := by
  intro t T gamma ht;
  have t_wt := And.left ht;
  have env_is_emp := And.right ht;
  induction t_wt with
  | var_rule _ _ _ pre =>
    rw [env_is_emp] at pre
    contradiction
  | abs_rule =>
    apply Or.intro_left
    apply value.abs
  | app_rule gamma e1 e2 T1 T2 pre1 pre2 ihe1 ihe2 =>
    cases e1 with
    | var x =>
      have env_is_not_emp := env_var_rule_noemp x (arrow T1 T2) gamma pre1
      contradiction
    | abs _ _ =>
      cases e2 with
      | var x =>
        have env_is_not_emp := env_var_rule_noemp x T1 gamma pre2
        contradiction
      | abs _ _ =>
        apply Or.intro_right
        apply Exists.intro
        apply e_app_abs
        apply value.abs
      | app _ _ =>
        apply Or.intro_right
        have r := And.intro pre2 env_is_emp;
        cases ihe2 r env_is_emp with
        | inl h1 =>
          contradiction
        | inr h2 =>
          cases h2 with
          | intro _ h =>
            apply Exists.intro
            apply e_app_right
            apply value.abs
            apply h
    | app _ _ =>
      apply Or.intro_right
      have r := And.intro pre1 env_is_emp;
      cases ihe1 r env_is_emp with
      | inl h1 =>
        contradiction
      | inr h2 =>
        cases h2 with
        | intro _ h =>
          apply Exists.intro
          apply e_app_left
          apply h

theorem subst_preservation : ∀ (s t : term) (x : Nat) (S T : type) (gamma : type_env),
  has_type gamma s S → has_type (List.cons (x, S) gamma) t T → has_type gamma (subst t x s) T := by
  sorry

theorem preservation : ∀ (e e' : term) (t : type) (gamma : type_env),
  has_type gamma e t → eval e e' → has_type gamma e' t := by
  intro e e' t gamma ht ev;
  induction ht with
  | var_rule _ _ _ pre =>
    contradiction
  | abs_rule =>
    contradiction
  | app_rule gamma e1 e2 T1 T2 pre1 pre2 ih1 ih2 =>
    cases ev with
    | e_app_abs T e v vv =>
      cases vv with
      | abs T b =>
        apply subst_preservation e b T T1
    | e_app_left e1 e1' e2' ev1 =>
      apply has_type.app_rule
      apply ihe1
      assumption
      assumption
      assumption
    | e_app_right v e2 e2' vv ev2 =>
      apply has_type.app_rule
      assumption
      apply ihe2
      assumption
      assumption
