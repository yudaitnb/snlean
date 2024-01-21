namespace Lambda

inductive Ty
| base : Ty
| arrow : Ty → Ty → Ty
deriving BEq, DecidableEq, Repr
open Ty
infixr:70 " :→ " => arrow


inductive Term
| var : String → Term
| lam : String → Ty → Term → Term
| app : Term → Term → Term
deriving BEq, DecidableEq, Repr
open Term
prefix:90 "` " => var
notation:50 "λ " x " : " T " ⬝ " d => lam x T d
infixr:min " $ " => app


def TyCtx := List (String × Ty) deriving BEq, DecidableEq, Repr
def nil : TyCtx := []
def extend : TyCtx → String → Ty → TyCtx := fun Γ x t => (x, t) :: Γ
notation "∅" => nil
def elem : TyCtx → (String × Ty) → Prop
| []         , _ => false
| (y, s) :: Γ, (x, t) => if x = y then t = s else elem Γ (x, t)
infix:50 " ∋ " => elem

inductive HasType : TyCtx → Term → Ty → Prop
| tyVar : (Γ ∋ (x, t)) → HasType Γ (var x) t
| tyAbs : HasType ((x, t1) :: Γ) e t2 → HasType Γ (λ x : t1 ⬝ e) (t1 :→ t2)
| tyApp : HasType Γ e1 (t2 :→ t1) → HasType Γ e2 t2 → HasType Γ (e1 $ e2) t1
open HasType
notation:40 Γ " ⊢ " t " : " ty:51 => HasType Γ t ty

inductive Value : Term → Prop
| lam : Value (λ x : T ⬝ e)

def subst : Term → String → Term → Term
| ` x, y, v => if x = y then v else ` x
| λ x : T ⬝ b, y, v => if x = y then λ x : T ⬝ b else λ x : T ⬝ (subst b y v)
| app l m, y, v => app (subst l y v) (subst m y v)
notation:90 " [ " x " := " v " ] " t => subst t x v

inductive Reduction : Term → Term → Prop
| eAppAbs : Value v → Reduction ((λ x : T ⬝ e) $ v) ([x := v] t)
| eAppLeft : Reduction e1 e1' → Reduction (e1 $ e2) (e1' $ e2)
| eAppRight : Value v → Reduction e2 e2' → Reduction (v $ e2) (v $ e2')
open Reduction
infix:40 " —→ " => Reduction
