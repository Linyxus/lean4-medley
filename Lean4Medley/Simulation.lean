namespace Simulation

inductive Typ : Type where
| nat : Typ
| arr : Typ -> Typ -> Typ
| prod : Typ -> Typ -> Typ

inductive Ctx : Type where
| empty : Ctx
| cons : Typ -> Ctx -> Ctx

inductive BoundVar : Ctx -> Typ -> Type where
| here : BoundVar (Ctx.cons T Γ0) T
| there : BoundVar Γ T -> BoundVar (Ctx.cons P Γ) T

inductive Trm : Ctx -> Typ -> Type where
| var : BoundVar Γ T -> Trm Γ T
| abs : Trm (Ctx.cons T Γ) U -> Trm Γ (Typ.arr T U)
| app : Trm Γ (Typ.arr T U) -> Trm Γ T -> Trm Γ U
| zero : Trm Γ Typ.nat
| succ : Trm Γ Typ.nat -> Trm Γ Typ.nat
| case :
  Trm Γ Typ.nat ->
  Trm Γ T ->
  Trm (Ctx.cons Typ.nat Γ) T ->
  Trm Γ T
| letin :
  Trm Γ T ->
  Trm (Ctx.cons T Γ) U ->
  Trm Γ U
| pair :
  Trm Γ T ->
  Trm Γ U ->
  Trm Γ (Typ.prod T U)
| proj1 :
  Trm Γ (Typ.prod T U) ->
  Trm Γ T
| proj2 :
  Trm Γ (Typ.prod T U) ->
  Trm Γ U
| pcase :
  Trm Γ (Typ.prod T U) ->
  Trm (Ctx.cons T (Ctx.cons U Γ)) V ->
  Trm Γ V

inductive IsVal : Trm Γ T -> Prop where
| abs : IsVal (Trm.abs t)
| zero : IsVal Trm.zero
| succ :
  IsVal t ->
  IsVal (Trm.succ t)
| pair :
  IsVal t ->
  IsVal u ->
  IsVal (Trm.pair t u)

theorem ext {Γ Δ : Ctx} {P : Typ}
  (f : ∀ {T}, BoundVar Γ T -> BoundVar Δ T) :
  ∀ {T}, BoundVar (Ctx.cons P Γ) T -> BoundVar (Ctx.cons P Δ) T := by
  intros T hb
  cases hb
  case here => constructor
  case there hb0 => constructor; apply f; trivial

theorem rename {Γ Δ : Ctx}
  (f : ∀ {T}, BoundVar Γ T -> BoundVar Δ T) :
  ∀ {T}, Trm Γ T -> Trm Δ T := by
  intros T ht
  induction ht generalizing Δ
  case var => apply Trm.var; apply f; trivial
  case abs ih =>
    apply Trm.abs
    apply ih
    apply ext; trivial
  case app ih1 ih2 =>
    apply Trm.app
    apply ih1; trivial
    apply ih2; trivial
  case zero => apply Trm.zero
  case succ ih => apply Trm.succ; apply ih; trivial
  case case ih1 ih2 ih3 =>
    apply Trm.case
    apply ih1; trivial
    apply ih2; trivial
    apply ih3; apply ext; trivial
  case letin ih1 ih2 =>
    apply Trm.letin
    apply ih1; trivial
    apply ih2; apply ext; trivial
  case pair ih1 ih2 =>
    apply Trm.pair
    apply ih1; trivial
    apply ih2; trivial
  case proj1 ih => apply Trm.proj1; apply ih; trivial
  case proj2 ih => apply Trm.proj2; apply ih; trivial
  case pcase ih1 ih2 =>
    apply Trm.pcase
    apply ih1; trivial
    apply ih2; apply ext; apply ext; trivial

inductive Reduce : Trm Γ T -> Trm Γ T -> Prop where
| apply_fun :
  Reduce t t' ->
  Reduce (Trm.app t u) (Trm.app t' u)
| apply_arg :
  IsVal t ->
  Reduce u u' ->
  Reduce (Trm.app t u) (Trm.app t u')

end Simulation
