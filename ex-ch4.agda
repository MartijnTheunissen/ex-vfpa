module ex-ch4 where

open import eq
open import nat
open import bool
open import list
open import product-thms

-- Excercise 4.1
{-
a) ∀ {ℓ} {A : Set ℓ} (l1 l2 : list A) → l1 ++ l2 ≡ l2 ++ l1 -- Can not be proven
b) ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (l : list A) → length (map f l) ≡ suc (length l) -- Can not be proven; length(map f l) ≡ (length l)
c) ∀ {ℓ} {A : Set ℓ } {p : A → 𝔹}{a : A}(n : ℕ) → p a ≡ ff → filter p (repeat n a) ≡ [] -- Provable
d) ∀ {ℓ} {A : Set ℓ} {l : list A) → is-empty l ≡ tt → is-empty (reverse l) ≡ ff -- Can not be proven
e) ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹)(l1 l2 : list A) → filter p (l1 ++ l2) ≡ filter p l1 ++ filter p l2 -- Provable
-}

-- Excercise 4.2
{-
a) (i), (iii), (iv), (v)
b) (i), (iii)
c) (i), (ii)
-}


-- Excercise 4.3
takeWhile : ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹) (l : list A) → list A
takeWhile p [] = []
takeWhile p (x :: l) = if p x then x :: takeWhile p l else []

-- Excercise 4.4
takerepeat : ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹) (a : A)(n : ℕ) → p a ≡ tt → takeWhile p (repeat n a) ≡ repeat n a
takerepeat p a zero r = refl
takerepeat p a (suc n) r with keep (p a)
takerepeat p a (suc n) r | t rewrite takerepeat p a n r | r = refl

-- Excercise 4.5
take : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (l : list A) → list A
take zero l = []
take (suc n) [] = []
take (suc n) (x :: l) = x :: take n l

-- Excercise 4.6
≡take++nthTail : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (l : list A) → (take n l) ++ (nthTail n l) ≡ l
≡take++nthTail zero l = refl
≡take++nthTail (suc n) [] = refl
≡take++nthTail (suc n) (x :: l) rewrite ≡take++nthTail n l = refl
