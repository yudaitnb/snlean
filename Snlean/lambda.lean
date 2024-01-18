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
| var_rule : ∀ (env : type_env) (x : Nat) (t : type), env.elem (x, t) → has_type env (var x) t
| abs_rule : ∀ (env : type_env) (x : Nat) (t1 t2 : type) (e : term), has_type ((x, t1) :: env) e t2 → has_type env (abs t1 e) (type.arrow t1 t2)
| app_rule : ∀ (env : type_env) (e1 e2 : term) (t2 t1 : type), has_type env e1 (type.arrow t2 t1) → has_type env e2 t2 → has_type env (app e1 e2) t1
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

theorem env_var_rule_noemp : ∀ (x : Nat) (T : type) (env : type_env), has_type env (var x) T → env ≠ [] := by
  intro x T env ht emp;
  cases ht with
  | var_rule _ _ _ nonemp =>
    rw [emp] at nonemp
    contradiction

theorem progress : ∀ (t : term) (T : type) (env : type_env), has_type env t T ∧ env = [] → value t ∨ (∃t' : term, eval t t') := by
  intro t T env ht;
  have h := And.left ht;
  have emp := And.right ht;
  induction h with
  | var_rule _ _ _ pre =>
    have nonemp := And.right ht;
    rw [nonemp] at pre
    contradiction
  | abs_rule =>
    apply Or.intro_left
    apply value.abs
  | app_rule env e1 e2 T1 T2 pre1 pre2 ihe1 ihe2 =>
    cases e1 with
    | var x =>
      have nonemp := env_var_rule_noemp x (arrow T1 T2) env pre1
      contradiction
    | abs _ _ =>
      cases e2 with
      | var x =>
        have nonemp := env_var_rule_noemp x T1 env pre2
        contradiction
      | abs _ _ =>
        apply Or.intro_right
        apply Exists.intro
        apply e_app_abs
        apply value.abs
      | app _ _ =>
        apply Or.intro_right
        have r := And.intro pre2 emp;
        cases ihe2 r emp with
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
      have r := And.intro pre1 emp;
      cases ihe1 r emp with
      | inl h1 =>
        contradiction
      | inr h2 =>
        cases h2 with
        | intro _ h =>
          apply Exists.intro
          apply e_app_left
          apply h

theorem preservation : ∀ (e e' : term) (t : type) (env : type_env), has_type env e t → eval e e' → has_type env e' t :=
  sorry
  -- arrow.intro
  -- induction ht
  --   -- var_rule
  --   _ x t env_elem
  --   -- abs_rule
  --   _ env x t1 t2 e ht ih
  --   -- app_rule
  --   _ env e1 e2 t1 t2 ht1 ht2 ih1 ih2,
    -- -- var_rule ケース
    -- -- 空の環境では変数は型付けできないので、このケースは発生しない
    -- { contradiction },

    -- -- abs_rule ケース
    -- -- 抽象化された項は値である
    -- { left, apply value.abs },

    -- -- app_rule ケース
    -- -- 関数適用のケースを考える
    -- -- e1 が値の場合、e2 が値であるか簡約可能であるかを考える
    -- -- e1 が値でない場合、e1 を簡約する
    -- { cases ih1 with v1 e1',
    --   -- e1 が値の場合
    --   { cases ih2 with v2 e2',
    --     -- e2 も値の場合
    --     { right, existsi subst e2 0 v1, apply eval.e_app_abs, assumption },
    --     -- e2 を簡約できる場合
    --     { right, cases e2' with e2' eval_e2, existsi app v1 e2', apply eval.e_app_right, assumption, assumption } },
    --   -- e1 を簡約できる場合
    --   { right, cases e1' with e1' eval_e1, existsi app e1' e2, apply eval.e_app_left, assumption } }

-- def x abs type.base (var 0)


#eval [1, 2].elem 3
