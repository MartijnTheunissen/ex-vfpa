module ex-ch3 where

open import nat
open import eq
open import nat-thms hiding (+perm ; *distribr ; *distribl)
open import bool
open import bool-thms using (𝔹-contra)

-- Excercise 3.1
+perm : ∀ (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
+perm zero y z = refl
+perm (suc x) y z rewrite +assoc x y z | +comm x y | +suc y (x + z) | +assoc y x z = refl

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z | +assoc z (x * z) (y * z) = refl

*distribl : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*distribl zero y z = refl
*distribl (suc x) y z rewrite *distribl x y z | +assoc (y + z) (x * y) (x * z) | +assoc (y  + x * y) z (x * z) | +comm y z | +comm (y + x * y) z | +assoc z y (x * y) = refl


-- Excercise 3.2
>-0 : ∀ (x : ℕ) → 0 > x ≡ ff
>-0 zero = refl
>-0 (suc x) = refl

>-suc : ∀ (n : ℕ) → suc n > n ≡ tt
>-suc zero = refl
>-suc (suc n) = >-suc n

>-trans : ∀ {x y z : ℕ} → y > x ≡ tt → z > y ≡ tt → z > x ≡ tt
>-trans {x} {0} p1 p2 rewrite >-0 x = 𝔹-contra p1
>-trans {y = suc y} {zero} p1 ()
>-trans {0} {suc y} {suc z} p1 p2 = refl
>-trans {suc x} {suc y} {suc z} p1 p2 = >-trans {x} p1 p2

>+ : ∀ {x y : ℕ} → y =ℕ 0 ≡ ff → y + x > x ≡ tt
>+ {y = zero} ()
>+ {x} {y = suc zero} p = >-suc x
>+ {x} {y = suc (suc y)} p = >-trans{x}{(suc y) + x}{suc ((suc y) + x)} (>+{x}{suc y} refl) (>-suc ((suc y) + x))

-- Excercise 3.3
-- a) iv: Compute factorial
-- b) i: Returns tt if n is even, ff is n is odd
