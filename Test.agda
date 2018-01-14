module Test where

open import Data.Fin
open import Data.List
open import Data.Product
open import Data.Vec
open import Data.Vec.All

open import Display
open import Game
open import Validation

open Game

g0 = freeCellGame
  ( []
  ∷ []
  ∷ []
  ∷ []
  ∷ [] )

  ( []
  ∷ []
  ∷ []
  ∷ ace of ♠ is moved þ []
  ∷ [] )

  ( three of ♠ is unmoved þ two of ♠ is unmoved þ []
  ∷ []
  ∷ []
  ∷ []
  ∷ []
  ∷ []
  ∷ []
  ∷ []
  ∷ [] )

g1 = makeLocMove {g = g0} {l = loc (# 8)} {l′ = loc (# 0)} (move (move start))
g2 = makeLocMove {g = g1} {l = loc (# 8)} {l′ = loc (# 7)} (move (move cons))
g3 = makeLocMove {g = g2} {l = loc (# 0)} {l′ = loc (# 7)} (move (move cons))

g3won : Won g3
g3won = searchWith (won? g3)
