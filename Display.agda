module Display where

open import Data.Digit using (digitChars)
open import Data.List as List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; _++_; unlines)
open import Data.Vec as Vec using (Vec)
open import Function

open import Game

displayRank : Rank → String
displayRank ace   = "A"
displayRank two   = "2"
displayRank three = "3"
displayRank four  = "4"
displayRank five  = "5"
displayRank six   = "6"
displayRank seven = "7"
displayRank eight = "8"
displayRank nine  = "9"
displayRank ten   = "10"
displayRank jack  = "J"
displayRank queen = "Q"
displayRank king  = "K"
displayRank (king+ ())

displaySuit : ∀ {c} → Suit c → String
displaySuit ♥ = "♥"
displaySuit ♢ = "♢"
displaySuit ♠ = "♠"
displaySuit ♣ = "♣"

displayCard : Card → String
displayCard (r of s is _) = displayRank r String.++ displaySuit s

displayPileType : PileType → String
displayPileType cascade = "cascade"
displayPileType foundation = "foundation"
displayPileType cell = "cell"

displayPileContents : List Card → String
displayPileContents = List.foldr _++_ "" ∘ List.intersperse " " ∘ List.map displayCard

displayLayout : Layout 16 → String
displayLayout
  = unlines
  ∘ Vec.toList
  ∘ Vec.zipWith (_++_ ∘ String.fromList ∘ List.[_]) digitChars
  ∘ Vec.map λ where
      (pt , cds) →
        " " ++ displayPileType pt ++ ": " ++ displayPileContents (List.reverse cds)

displayGame : Game 16 → String
displayGame (game {layout = layout} _) = displayLayout layout

{-# DISPLAY game {layout = layout} piles = layout #-}
