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

theorem Trm.weaken (ht : Trm Γ T) (P : Typ) : Trm (Ctx.cons P Γ) T :=
  rename (fun hb => BoundVar.there hb) ht

theorem exts {Γ Δ : Ctx} {P : Typ}
  (σ : ∀ {T}, BoundVar Γ T -> Trm Δ T) :
  ∀ {T}, BoundVar (Ctx.cons P Γ) T -> Trm (Ctx.cons P Δ) T := by
  intros T hb
  cases hb
  case here => apply Trm.var; constructor
  case there hb0 =>
    apply Trm.weaken
    apply σ; trivial

theorem subst {Γ Δ : Ctx}
  (σ : ∀ {T}, BoundVar Γ T -> Trm Δ T) :
  ∀ {T}, Trm Γ T -> Trm Δ T := by
  intros T ht
  induction ht generalizing Δ
  case var => apply σ; trivial
  case abs ih =>
    apply Trm.abs
    apply ih
    apply exts; trivial
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
    apply ih3; apply exts; trivial
  case letin ih1 ih2 =>
    apply Trm.letin
    apply ih1; trivial
    apply ih2; apply exts; trivial
  case pair ih1 ih2 =>
    apply Trm.pair
    apply ih1; trivial
    apply ih2; trivial
  case proj1 ih => apply Trm.proj1; apply ih; trivial
  case proj2 ih => apply Trm.proj2; apply ih; trivial
  case pcase ih1 ih2 =>
    apply Trm.pcase
    apply ih1; trivial
    apply ih2; apply exts; apply exts; trivial

theorem subst_param
  (t : Trm (Ctx.cons T Γ) U)
  (u : Trm Γ T) :
  Trm Γ U := by
  apply subst
  case a => exact t
  case σ =>
    intros T hb
    cases hb
    case here => exact u
    case there hb0 => apply Trm.var; exact hb0

theorem subst_param2
  (t : Trm (Ctx.cons T1 (Ctx.cons T2 Γ)) U)
  (u1 : Trm Γ T1) (u2 : Trm Γ T2) :
  Trm Γ U := by
  apply subst
  case a => exact t
  case σ =>
    intros T hb
    cases hb
    case here => trivial
    case there hb =>
      cases hb <;> try (solve | trivial)
      constructor; trivial

inductive Reduce : Trm Γ T -> Trm Γ T -> Prop where
| apply_fun :
  Reduce t t' ->
  Reduce (Trm.app t u) (Trm.app t' u)
| apply_arg :
  IsVal t ->
  Reduce u u' ->
  Reduce (Trm.app t u) (Trm.app t u')
| apply :
  Reduce (Trm.app (Trm.abs t) u) (subst_param t u)
| succ :
  Reduce t t' ->
  Reduce (Trm.succ t) (Trm.succ t')
| case_ctx :
  Reduce t t' ->
  Reduce (Trm.case t u1 u2) (Trm.case t' u1 u2)
| case_zero :
  Reduce (Trm.case Trm.zero u1 u2) u1
| case_succ :
  IsVal t ->
  Reduce (Trm.case (Trm.succ t) u1 u2) (subst_param u2 t)
| letin_ctx :
  Reduce t t' ->
  Reduce (Trm.letin t u) (Trm.letin t' u)
| letin :
  IsVal v ->
  Reduce (Trm.letin v u) (subst_param u v)
| pair_left :
  Reduce t t' ->
  Reduce (Trm.pair t u) (Trm.pair t' u)
| pair_right :
  IsVal t ->
  Reduce u u' ->
  Reduce (Trm.pair t u) (Trm.pair t u')
| proj1_ctx :
  Reduce t t' ->
  Reduce (Trm.proj1 t) (Trm.proj1 t')
| proj1 :
  IsVal t ->
  IsVal u ->
  Reduce (Trm.proj1 (Trm.pair t u)) t
| proj2_ctx :
  Reduce t t' ->
  Reduce (Trm.proj2 t) (Trm.proj2 t')
| proj2 :
  IsVal t ->
  IsVal u ->
  Reduce (Trm.proj2 (Trm.pair t u)) u
| pcase_ctx :
  Reduce t t' ->
  Reduce (Trm.pcase t u) (Trm.pcase t' u)
| pcase :
  IsVal t ->
  IsVal u ->
  Reduce (Trm.pcase (Trm.pair t u) v) (subst_param2 v t u)

end Simulation
