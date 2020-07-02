module transitivity-rel where

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

data Thing : Set where
  A : Thing
  B : Thing
  C : Thing
  D : Thing

data _R_ : Thing → Thing → Set where 
  AB : A R B
  CD : C R D
  SYM : {a b : Thing} → a R b → b R a
  TRS : {a b c : Thing} → a R b → b R c → a R c
  RFL : {a : Thing} → a R a

ac : ¬ (A R C)
ca : ¬ (C R A)
bc : ¬ (B R C)
cb : ¬ (C R B)
da : ¬ (D R A)
ad : ¬ (A R D)

ac (SYM x) = ca x
ac (TRS AB x₁) = bc x₁
ac (TRS {b = A} (SYM {a = .A} x) x₁) = ac x₁
ac (TRS {b = B} (SYM {a = .B} x) x₁) = bc x₁
ac (TRS {b = C} (SYM {a = .C} x) x₁) = ca x
ac (TRS {b = D} (SYM {a = .D} x) x₁) = da x
ac (TRS {b = A} (TRS {b = A} {c = .A} x x₂) x₁) = ac x₁
ac (TRS {b = B} (TRS {b = A} {c = .B} x x₂) x₁) = bc x₁
ac (TRS {b = C} (TRS {b = A} {c = .C} x x₂) x₁) = {!!}
ac (TRS {b = D} (TRS {b = A} {c = .D} x x₂) x₁) = {!!}
ac (TRS {b = A} (TRS {b = B} {c = .A} x x₂) x₁) = {!!}
ac (TRS {b = B} (TRS {b = B} {c = .B} x x₂) x₁) = {!!}
ac (TRS {b = C} (TRS {b = B} {c = .C} x x₂) x₁) = {!!}
ac (TRS {b = D} (TRS {b = B} {c = .D} x x₂) x₁) = {!!}
ac (TRS {b = A} (TRS {b = C} {c = .A} x x₂) x₁) = {!!}
ac (TRS {b = B} (TRS {b = C} {c = .B} x x₂) x₁) = {!!}
ac (TRS {b = C} (TRS {b = C} {c = .C} x x₂) x₁) = {!!}
ac (TRS {b = D} (TRS {b = C} {c = .D} x x₂) x₁) = {!!}
ac (TRS {b = A} (TRS {b = D} {c = .A} x x₂) x₁) = {!!}
ac (TRS {b = B} (TRS {b = D} {c = .B} x x₂) x₁) = {!!}
ac (TRS {b = C} (TRS {b = D} {c = .C} x x₂) x₁) = {!!}
ac (TRS {b = D} (TRS {b = D} {c = .D} x x₂) x₁) = {!!}
ac (TRS RFL x₁) = ac x₁

ca (SYM x) = ac x
ca (TRS CD x₁) = da x₁
ca (TRS (SYM x) x₁) = {!!}
ca (TRS (TRS x x₂) x₁) = {!!}
ca (TRS RFL x₁) = ca x₁


data _R'_ : Thing → Thing → Set where
  AB : A R' B
  BA : B R' A
  CD : C R' D
  DC : D R' C
  RFL : {a : Thing} → a R' a

R'-sym : {a b : Thing} → a R' b → b R' a
R'-sym {.A} {.B} AB = BA
R'-sym {.B} {.A} BA = AB
R'-sym {.C} {.D} CD = DC
R'-sym {.D} {.C} DC = CD
R'-sym {a} {b} RFL = RFL

R'-trans : {a b c : Thing} → a R' b → b R' c → a R' c
R'-trans {.A} {.B} {.A} AB BA = RFL
R'-trans {.B} {.A} {.B} BA AB = RFL
R'-trans {.C} {.D} {.C} CD DC = RFL
R'-trans {.D} {.C} {.D} DC CD = RFL
R'-trans {a} {b} r RFL = r
R'-trans {a} {.a} RFL r' = r'

_ : ¬ (A R' C)
_ = λ ()
