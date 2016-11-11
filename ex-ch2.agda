module ex-ch2 where

open import bool
open import eq

-- Excercise 2.1
||-cong₂ : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
||-cong₂ {tt} p = refl
||-cong₂ {ff} p = p

𝔹-contra : ff ≡ tt → ∀ {ℓ} {P : Set ℓ} → P
𝔹-contra ()

&&-fst : {b1 b2 : 𝔹} → b1 && b2 ≡ tt → b1 ≡ tt
&&-fst {tt} p = refl
&&-fst {ff} p rewrite p = refl -- or &&-fst {ff} p = p

&&-combo : {p1 p2 : 𝔹} → p1 ≡ tt → p2 ≡ tt → p1 && p2 ≡ tt
&&-combo p q rewrite p = q


-- Excercise 2.2
imp-transp : {a b : 𝔹} → a imp b ≡ ~ b imp ~ a
imp-transp {tt}{tt} = refl
imp-transp {tt}{ff} = refl
imp-transp {ff}{tt} = refl
imp-transp {ff}{ff} = refl

-- Excercise 2.3
-- a, b, d, e

-- forumla f can only be proven by refl if &&' (see below) is used instead of && in bool.agda

-- example:
_&&'_ : 𝔹 → 𝔹 → 𝔹
x &&' tt = x
x &&' ff = ff

ex2-3f-test : {x : 𝔹} → x &&' tt ≡ x
ex2-3f-test = refl
