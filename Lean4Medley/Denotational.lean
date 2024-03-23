namespace Denotational

inductive Typ : Type where
| any : Typ

inductive Context : Type where
| empty : Context
| cons : Context → Typ → Context

inductive Var : Context -> Typ -> Type where
| here : Var (Context.cons Γ T) T
| there :
  Var Γ T ->
  Var (Context.cons Γ T') T

inductive Term : Context -> Typ -> Type where
| var :
  Var Γ T ->
  Term Γ T
| lam :
  Term (Context.cons Γ Typ.any) Typ.any ->
  Term Γ Typ.any
| app :
  Term Γ Typ.any ->
  Term Γ Typ.any ->
  Term Γ Typ.any

def Context.length : Context -> Nat
| Context.empty => 0
| Context.cons Γ _ => 1 + Γ.length

inductive Value : Type where
| bot : Value
| mapping : Value -> Value -> Value
| union : Value -> Value -> Value

inductive Subvalue : Value -> Value -> Prop where
| bot :
  Subvalue Value.bot v
| conj_left :
  Subvalue v w ->
  Subvalue u w ->
  Subvalue (Value.union v u) w
| conj_right_l :
  Subvalue v w ->
  Subvalue v (Value.union u w)
| conj_right_r :
  Subvalue v w ->
  Subvalue v (Value.union w u)
| trans :
  Subvalue v w ->
  Subvalue w u ->
  Subvalue v u

end Denotational
