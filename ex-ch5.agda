module ex-ch5 where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

-- Excercise 5.1
_by_matrix : ℕ → ℕ → Set
n by m matrix = Vec (Vec ℕ m) n


-- Excercise 5.2 a)
zero-vector : (n : ℕ) → Vec ℕ n
zero-vector zero = []
zero-vector (suc n) = 0 ∷ zero-vector n


zero-matrix : (n : ℕ) (m : ℕ) → n by m matrix
zero-matrix zero m = []
zero-matrix (suc n) m = zero-vector m ∷ zero-matrix n m

-- Excercise 5.2 b)
matrix-elt : {n m : ℕ} (mat : n by m matrix) (row : ℕ) (col : ℕ) → row < n → col < m → ℕ
matrix-elt {zero} mat row col () x₁
matrix-elt {suc n} {zero} mat row col x ()
matrix-elt {suc n} {suc m} ((x ∷ mat) ∷ mat₁) zero zero x₁ x₂ = x
matrix-elt {suc n} {suc m} ((x ∷ mat) ∷ mat₁) zero (suc col) x₁ (s≤s x₂) = matrix-elt {1} {m} (mat ∷ []) zero col (s≤s z≤n) x₂
matrix-elt {suc n} {suc m} ((x ∷ mat) ∷ mat₁) (suc row) col (s≤s x₁) x₂ = matrix-elt {n} {suc m} mat₁ row col x₁ x₂

matrix₁ : 1 by 3 matrix
matrix₁ = (1 ∷ 2 ∷ 3 ∷ []) ∷ []

matrix₂ : 2 by 3 matrix
matrix₂ = (11 ∷ 12 ∷ 13 ∷ [])
          ∷ (21 ∷ 22 ∷ 23 ∷ []) ∷ []

test : matrix-elt matrix₂ 1 2 (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) ≡ 23
test = refl

-- Excercise 5.2 c)
set-vector-el : ∀{ℓ} {A : Set ℓ}{n : ℕ} → Vec A n → (pos : ℕ) → A → pos < n → Vec A n
set-vector-el [] pos el ()
set-vector-el (x ∷ vec) zero el x₁ = el ∷ vec
set-vector-el (x ∷ vec) (suc pos) el (s≤s x₁) = x ∷ (set-vector-el vec pos el x₁)

vec₁ : Vec ℕ 3
vec₁ = 2 ∷ 3 ∷ 4 ∷ []

vec-test : (set-vector-el vec₁ 2 0 (s≤s (s≤s (s≤s z≤n))) ) ≡ 2 ∷ 3 ∷ 0 ∷ []
vec-test  = refl

set-matrix-el : {n m : ℕ} (mat : n by m matrix) (row : ℕ) (col : ℕ) (el : ℕ) → row < n → col < m →  n by m matrix
set-matrix-el {zero} mat row col el () p'
set-matrix-el {suc n} (vec ∷ mat) zero col el p p' = (set-vector-el vec col el p') ∷ mat
set-matrix-el {suc n} (vec ∷ mat) (suc row) col el (s≤s p) p' = vec ∷ (set-matrix-el {n} mat row col el p p')

n<sucn : {n : ℕ} → n < suc n
n<sucn {zero} = s≤s z≤n
n<sucn {suc n} = s≤s n<sucn

≤extrasuc : ∀ {n m} → suc n ≤ m → suc n ≤ suc m
≤extrasuc {zero} p = s≤s z≤n
≤extrasuc {suc n} {zero} ()
≤extrasuc {suc n} {suc m} (s≤s p) = s≤s (≤extrasuc p)

m∸n<sucm : ∀ {m n} → m ∸ n < suc m
m∸n<sucm {m} {n} with n∸m≤n
... | r = s≤s (r n m)

set-diagonal-helper : {n m : ℕ} (mat : n by m matrix) (d : ℕ) (iter : ℕ) → iter < m → iter < n → n by m matrix
set-diagonal-helper {m = zero} mat d iter ()
set-diagonal-helper {zero} {suc m} mat d iter p ()
set-diagonal-helper {suc n} {suc m} (vec ∷ mat) d zero p p' = (set-vector-el vec m d n<sucn) ∷ mat
set-diagonal-helper {suc n} {suc m} (vec ∷ mat) d (suc iter) (s≤s p) (s≤s p') =
                       (set-vector-el vec (m ∸ (suc iter)) d ((m∸n<sucm {m} {suc iter})) )
                       ∷ set-diagonal-helper {n}{suc m} mat d iter (≤extrasuc p) p'

set-diagonal : {n : ℕ} (mat : n by n matrix) (d : ℕ) → n by n matrix
set-diagonal {zero} mat d = []
set-diagonal {suc n} mat d = set-diagonal-helper {suc n} {suc n} mat d n n<sucn n<sucn

diagonal-matrix : (d n : ℕ) → n by n matrix
diagonal-matrix d n = set-diagonal (zero-matrix n n) d

test₁ : diagonal-matrix 42 1 ≡ ((42 ∷ []) ∷ [])
test₁ = refl

matrix₄ : 4 by 4 matrix
matrix₄ =   (10 ∷ 0 ∷ 0 ∷ 0 ∷ [])
          ∷ (0 ∷ 10 ∷ 0 ∷ 0 ∷ [])
          ∷ (0 ∷ 0 ∷ 10 ∷ 0 ∷ [])
          ∷ (0 ∷ 0 ∷ 0 ∷ 10 ∷ []) ∷ []

test₂ : matrix₄ ≡ diagonal-matrix 10 4
test₂ = refl

matrix₅ : 5 by 5 matrix
matrix₅ =   (1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
          ∷ (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])
          ∷ (0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ [])
          ∷ (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ [])
          ∷ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []) ∷ []

identity-matrix : (n : ℕ) → n by n matrix
identity-matrix n = diagonal-matrix 1 n

test₃ : matrix₅ ≡ identity-matrix 5
test₃ = refl

-- Excercise 5.2 d)
nby0matrix : (n : ℕ) → n by 0 matrix
nby0matrix zero = []
nby0matrix (suc n) = [] ∷ nby0matrix n

transpose : {n m : ℕ} → n by m matrix → m by n matrix
transpose {m = m} [] = nby0matrix m
transpose (vec ∷ mat) = zipWith _∷_ vec (transpose mat)

matrix₆ : 2 by 3 matrix
matrix₆ =   (1 ∷ 2 ∷ 3 ∷ [])
          ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []

matrix₆-transposed : 3 by 2 matrix
matrix₆-transposed =  (1 ∷ 4 ∷ [])
                    ∷ (2 ∷ 5 ∷ [])
                    ∷ (3 ∷ 6 ∷ []) ∷ []

test₄ : matrix₆ ≡ transpose (matrix₆-transposed)
test₄ = refl

test₅ : transpose matrix₆ ≡ matrix₆-transposed
test₅ = refl

-- Excercise 5.2 e)
_∙_ : {n : ℕ} → Vec ℕ n → Vec ℕ n → ℕ
[] ∙ [] = zero
(x₁ ∷ vec₁) ∙ (x₂ ∷ vec₂) = (x₁ * x₂) + (vec₁ ∙ vec₂)

vec₂ : Vec ℕ 3
vec₂ = 1 ∷ 2 ∷ 3 ∷ []

vec₃ : Vec ℕ 3
vec₃ = 4 ∷ 5 ∷ 6 ∷ []

test₆ : vec₂ ∙ vec₃ ≡ 32
test₆ = refl

test₇ : vec₃ ∙ vec₂ ≡ 32
test₇ = refl

-- Excercise 5.2 f)
vec-at : {n : ℕ} → Vec ℕ n → (pos : ℕ) → pos < n → ℕ
vec-at [] pos ()
vec-at (x ∷ vec) zero p = x
vec-at (x ∷ vec) (suc pos) (s≤s p) = vec-at vec pos p

mat-multiplied-row : {k m : ℕ} → Vec ℕ k → m by k matrix → Vec ℕ m
mat-multiplied-row vec [] = []
mat-multiplied-row vec₁ (vec₂ ∷ mat) = (vec₁ ∙ vec₂) ∷ mat-multiplied-row vec₁ mat

_*matrix_ : {n k m : ℕ} → n by k matrix → k by m matrix → n by m matrix
[] *matrix mat₂ = []
_*matrix_ {suc n}{k}{m} (vec ∷ mat₁) mat₂ = (mat-multiplied-row vec (transpose mat₂)) ∷ mat₁ *matrix mat₂


test₈ : (diagonal-matrix 10 4) *matrix (identity-matrix 4) ≡ (diagonal-matrix 10 4)
test₈ = refl

test₉ : matrix₆ *matrix (identity-matrix 3) ≡ matrix₆
test₉ = refl

-- Excercise 5.3

{-
-- This works (using the Iowa Agda Library)
𝕍-to-𝕃-to-𝕍 : ∀ {ℓ} {n : ℕ} {A : Set ℓ} (vec : 𝕍 A n) → 𝕃-to-𝕍 (𝕍-to-𝕃 vec) ≡ (n , vec)
𝕍-to-𝕃-to-𝕍 [] = refl
𝕍-to-𝕃-to-𝕍 {n = suc n} (x :: vec) rewrite 𝕍-to-𝕃-to-𝕍 vec = refl
-}

-- This does not work. Agda complains with:
-- n != Data.List.Base.foldr (λ _ → suc) 0 (toList vec) of type ℕ
-- When checking that the expression vec has type Vec A (.Data.List.Base.length (toList vec))

-- vec-list-vec-same : ∀ {ℓ} {n : ℕ} {A : Set ℓ} (vec : Vec A n) → fromList (toList vec) ≡ vec
-- vec-list-vec-same = ?
