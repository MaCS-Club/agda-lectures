module Nat where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero * _ = zero
suc n * m = m + n * m
{-# BUILTIN NATTIMES _*_ #-}
