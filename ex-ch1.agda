module ex-ch1 where

open import bool hiding (_xor_)

-- Excercises of chapter 1

{- Excercise 1.1
a) tt
b) ff
c) ff
-}

{- Excercise 1.2
a) 𝔹
b) 𝔹
c) 𝔹 → 𝔹 → 𝔹
d) Set
-}

-- Excercise 1.3
_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor tt = ff
ff xor ff = ff
_ xor _   = tt

-- Excercise 1.4
data day : Set where
  mon : day
  tue : day
  wed : day
  thu : day
  fri : day
  sat : day
  sun : day

-- Excercise 1.5
nextday : day → day
nextday mon = tue
nextday tue = wed
nextday wed = thu
nextday thu = fri
nextday fri = sat
nextday sat = sun
nextday sun = mon

-- Excercise 1.6
data suit : Set where
  hearts : suit
  clubs : suit
  spades : suit
  diamonds : suit

-- Excercise 1.7
is-red : suit → 𝔹
is-red hearts = tt
is-red diamonds = tt
is-red _ = ff
